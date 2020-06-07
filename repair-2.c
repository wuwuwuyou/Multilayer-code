/* *
 * Copyright (c) 2014, James S. Plank and Kevin Greenan
 * All rights reserved.
 *
 * Jerasure - A C/C++ Library for a Variety of Reed-Solomon and RAID-6 Erasure
 * Coding Techniques
 *
 * Revision 2.0: Galois Field backend now links to GF-Complete
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *  - Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *  - Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 *  - Neither the name of the University of Tennessee nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
 * WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/* Jerasure's authors:

   Revision 2.x - 2014: James S. Plank and Kevin M. Greenan.
   Revision 1.2 - 2008: James S. Plank, Scott Simmerman and Catherine D. Schuman.
   Revision 1.0 - 2007: James S. Plank.
 */

/* 
This program takes as input an inputfile, k, m, a coding
technique, w, and packetsize.  It is the companion program
of encoder.c, which creates k+m files.  This program assumes 
that up to m erasures have occurred in the k+m files.  It
reads in the k+m files or marks the file as erased. It then
recreates the original file and creates a new file with the
suffix "decoded" with the decoded contents of the file.

This program does not error check command line arguments because 
it is assumed that encoder.c has been called previously with the
same arguments, and encoder.c does error check.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <signal.h>
#include <unistd.h>
#include "jerasure.h"
#include "reed_sol.h"
#include "galois.h"
#include "cauchy.h"
#include "liberation.h"
#include "timing.h"

#define N 10
#define M 8

enum Coding_Technique {Reed_Sol_Van, Reed_Sol_R6_Op, Cauchy_Orig, Cauchy_Good, Liberation, Blaum_Roth, Liber8tion, RDP, EVENODD, No_Coding};

char *Methods[N] = {"reed_sol_van", "reed_sol_r6_op", "cauchy_orig", "cauchy_good", "liberation", "blaum_roth", "liber8tion", "rdp", "evenodd", "no_coding"};

/* Global variables for signal handler */
enum Coding_Technique method;
int readins, n;

/* Function prototype */
void ctrl_bs_handler(int dummy);

int main (int argc, char **argv) {
	FILE *fp;				// File pointer

	/* Jerasure arguments */
	char **data;
	char **coding;
	int *erasures;
	int *erased;
	int *matrix;
	int *bitmatrix;
	
	char **tempcoding;
	char **tempdata;
	char *e;
	char *e1;
	/* Parameters */
	int k, m, w, packetsize, buffersize;
	int tech;
	char *c_tech;
	int jj=0;
	int i, j,i1,j1,i2,i4,i5;				// loop control variable, s
	int blocksize = 0;			// size of individual files
	int origsize;			// size of file before padding
	int total;				// used to write data, not padding to file
	struct stat status;		// used to find size of individual files
	int numerased;			// number of erased files
		
	/* Used to recreate file names */
	char *temp;
	char *cs1, *cs2, *extension;
	char *fname;
	char *fname1;
	int md;
	char *curdir;

	/* Used to time decoding */
	struct timing t1, t2, t3, t4,q1,q2,q3,q4,q5,q6;
	//double tsec;
	double save_value_time;
	double bit_operation_time;
	double repair_time;
	double sum_time;
	double matrix_time;
	
	signal(SIGQUIT, ctrl_bs_handler);

	matrix = NULL;
	bitmatrix = NULL;
	
	
	/* Start timing */
	

	/* Error checking parameters */
	if (argc != 2) {
		fprintf(stderr, "usage: inputfile\n");
		exit(0);
	}
	curdir = (char *)malloc(sizeof(char)*1000);
	assert(curdir == getcwd(curdir, 1000));
	
	/* Begin recreation of file names */
	cs1 = (char*)malloc(sizeof(char)*strlen(argv[1]));
	cs2 = strrchr(argv[1], '/');
	if (cs2 != NULL) {
		cs2++;
		strcpy(cs1, cs2);
	}
	else {
		strcpy(cs1, argv[1]);
	}
	cs2 = strchr(cs1, '.');
	if (cs2 != NULL) {
                extension = strdup(cs2);
		*cs2 = '\0';
	} else {
           extension = strdup("");
        }	
	fname = (char *)malloc(sizeof(char*)*(100+strlen(argv[1])+20));

	/* Read in parameters from metadata file */
	sprintf(fname, "%s/Coding/%s_meta.txt", curdir, cs1);

	fp = fopen(fname, "rb");
        if (fp == NULL) {
          fprintf(stderr, "Error: no metadata file %s\n", fname);
          exit(1);
        }
	temp = (char *)malloc(sizeof(char)*(strlen(argv[1])+20));
	if (fscanf(fp, "%s", temp) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	
	if (fscanf(fp, "%d", &origsize) != 1) {
		fprintf(stderr, "Original size is not valid\n");
		exit(0);
	}
	if (fscanf(fp, "%d %d %d %d %d", &k, &m, &w, &packetsize, &buffersize) != 5) {
		fprintf(stderr, "Parameters are not correct\n");
		exit(0);
	}
	c_tech = (char *)malloc(sizeof(char)*(strlen(argv[1])+20));
	if (fscanf(fp, "%s", c_tech) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	if (fscanf(fp, "%d", &tech) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	method = tech;
	if (fscanf(fp, "%d", &readins) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	fclose(fp);	

	/* Allocate memory */
	erased = (int *)malloc(sizeof(int)*(k+m));
	for (i = 0; i < k+m; i++)
		erased[i] = 0;
	erasures = (int *)malloc(sizeof(int)*(k+m));

	data = (char **)malloc(sizeof(char *)*k);
	coding = (char **)malloc(sizeof(char *)*m);
	tempdata = (char **)malloc(sizeof(char *)*k);
	tempcoding = (char **)malloc(sizeof(char *)*m);
	e = (char *)malloc(sizeof(char *)*7);
	e1 = (char *)malloc(sizeof(char *)*7);			
	if (buffersize != origsize) {
		for (i = 0; i < k; i++) {
			data[i] = (char *)malloc(sizeof(char)*(buffersize/k));
			tempdata[i] = (char *)malloc(sizeof(char *)*(buffersize/k));
		}
		for (i = 0; i < m; i++) {
			coding[i] = (char *)malloc(sizeof(char)*(buffersize/k));
			tempcoding[i] = (char *)malloc(sizeof(char)*(buffersize/k));
		}
		blocksize = buffersize/k;
	}

	sprintf(temp, "%d", k);
	md = strlen(temp);
	
        printf("buffersize:%d\n", buffersize);
 	 printf("origsize:%d\n", origsize);  
	
	/* Allow for buffersize and determine 
	/* Create coding matrix or bitmatrix */
	
	switch(tech) {
		case No_Coding:
			break;
		case Reed_Sol_Van:
			matrix = reed_sol_vandermonde_coding_matrix(k, m, w);
			break;
		case Reed_Sol_R6_Op:
			matrix = reed_sol_r6_coding_matrix(k, w);
			break;
		case Cauchy_Orig:
			matrix = cauchy_original_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			break;
		case Cauchy_Good:
			matrix = cauchy_good_general_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			break;
		case Liberation:
			bitmatrix = liberation_coding_bitmatrix(k, w);
			break;
		case Blaum_Roth:
			bitmatrix = blaum_roth_coding_bitmatrix(k, w);
			break;
		case Liber8tion:
			bitmatrix = liber8tion_coding_bitmatrix(k);
	}
	
	printf("matrix: \n");
	jerasure_print_matrix(matrix,k+m,k,w);
printf("\n");
//print_data_and_coding(k, m, w, sizeof(long), data, coding);
printf( " 0\n");


	/* Begin decoding process */
	total = 0;
	n = 1;	
	while (n <= readins) {
		numerased = 0;
		/* Open files, check for erasures, read in data/coding */	
			
		for (i = 0; i < k; i++) {
			sprintf(fname, "%s/Coding/%s_k%0*d%s", curdir, cs1, md, i, extension);
			fp = fopen(fname, "rb");
			if (fp == NULL) {
				erased[i] = 1;
				erasures[numerased] = i;
				numerased++;}
				
			else {
				if (buffersize == origsize) {
					stat(fname, &status);
					blocksize = status.st_size/M;
					
					data[i] = (char *)malloc(sizeof(char)*blocksize);
					tempdata[i] = (char *)malloc(sizeof(char)*M*blocksize);
					assert(M*blocksize == fread(tempdata[i], sizeof(char), M*blocksize, fp));
				}
				
				fclose(fp);
			}
		}
				
					
		for (i = 0; i < m; i++) {
			sprintf(fname, "%s/Coding/%s_m%0*d%s", curdir, cs1, md, i, extension);
				fp = fopen(fname, "rb");
				if (fp == NULL) {
				erased[k+i] = 1;
				erasures[numerased] = k+i;
				numerased++;}	
			else{
				if (buffersize == origsize) {
					stat(fname, &status);
					blocksize = status.st_size/M;
					
					coding[i] = (char *)malloc(sizeof(char)*blocksize);
					tempcoding[i] = (char *)malloc(sizeof(char)*M*blocksize);
					assert(M*blocksize == fread(tempcoding[i], sizeof(char), M*blocksize, fp));
				}
					
				fclose(fp);
			}
		}
printf("\n");
printf("blocksize:%d\n", blocksize);
printf("\n");
	/* Finish allocating data/coding if needed */
		if (n == 1) {
			for (i = 0; i < numerased; i++) {
				if (erasures[i] < k) {
					data[erasures[i]] = (char *)malloc(sizeof(char)*blocksize);
					tempdata[erasures[i]] = (char *)malloc(sizeof(char)*M*blocksize);
				}
				else {
					coding[erasures[i]-k] = (char *)malloc(sizeof(char)*blocksize);
					tempcoding[erasures[i]-k] = (char *)malloc(sizeof(char)*M*blocksize);
				}
			}
		}
		erasures[numerased] = -1;

printf( " 1\n");

char **fdata;
char **fcoding;
fdata = (char **)malloc(sizeof(char*)*M);
fcoding = (char **)malloc(sizeof(char*)*M);
for(j = 0; j < M; j++) {
fdata[j] = (char *)malloc(sizeof(char)*k*blocksize);
fcoding[j] = (char *)malloc(sizeof(char)*m*blocksize);}

printf( " 2\n");
                 	for(i=0;i<M;i++){
                 	for(j1=0;j1<k;j1++){
                 	for(j=0;j<blocksize;j++){           
                	fdata[i][j+j1*blocksize]=*(tempdata[j1]+j+i*blocksize);}}}
                  	
   		

printf( " 3\n");
     			 for(i=0;i<M;i++){
    			 for(j1=0;j1<m;j1++){
      			 for(j=0;j<blocksize;j++){
      			 fcoding[i][j+j1*blocksize]=*(tempcoding[j1]+i*blocksize+j);}}}
printf( " --------------\n");

			 printf("\n fdata 4*10: char \n ");
		        for(i1=0;i1<8;i1++){
		        for(j=0;j<10;j++){
			printf(" %d ",fdata[i1][j*blocksize]);}
			printf("\n");	}

			printf("\n fcoding 4*2: char \n ");
		        for(i1=0;i1<8;i1++){
		        for(j=0;j<2;j++){
			printf(" %d ",fcoding[i1][j*blocksize]);}
			printf("\n");	}



timing_set(&t1);

   			char  **Eextra;
			Eextra = (char **)malloc(sizeof(char*)*4);
			for(j = 0; j < 4; j++) {
			Eextra[j] = (char *)malloc(sizeof(char)*blocksize);} 
			char  **Eextra1;
			Eextra1 = (char **)malloc(sizeof(char*)*4);
			for(j = 0; j < 4; j++) {
			Eextra1[j] = (char *)malloc(sizeof(char)*blocksize);} 
			
			//save the original value
			for(j=0;j<4;j++) {
			for(i1=0;i1<blocksize;i1++){
			Eextra[j][i1]=*(fdata[2*j]+1*blocksize+i1);}}//node1 original value not loaded                     
		
			for(j=0;j<4;j++) {
			for(i1=0;i1<blocksize;i1++){
			Eextra1[j][i1]=Eextra[j][i1];}}//node1 original value not loaded

timing_set(&t2);


timing_set(&q1);
char **extra;
extra = (char **)malloc(sizeof(char*)*64);
for(i = 0; i < 64; i++) {
extra[i] = (char *)malloc(sizeof(char)*blocksize);}




////////////////////	




 for(i=0;i<7;i++){
               e[0]=20; e[1]=18;e[2]=21;e[3]=16;e[4]=25;e[5]=13;e[6]=54;}   
      for(i=0;i<7;i++){
               e1[0]=1; e1[1]=1;e1[2]=1;e1[3]=1;e1[4]=1;e1[5]=1;e1[6]=1;}
      galois_region_xor(e,e1,7);

/*for(i=0;i<M;i++){//i=0 2 4 6 8 10 12 14 16..............	
if( i%2 == 0){

for(i1 = 0; i1< blocksize; i1++){
extra[i/2][i1]=*(fdata[i+1] + i1);}


galois_w8_region_xor(fdata[i+1],(fdata[i] + blocksize),blocksize);
			

galois_w08_region_multiply((fdata[i] + blocksize), galois_single_divide(1,e1[0],w), blocksize, (fdata[i] + blocksize), 0);

			
galois_w08_region_multiply((fdata[i] + blocksize),e[0], blocksize, (fdata[i+1]), 0);


galois_w8_region_xor(extra[i/2],fdata[i+1],blocksize);//a 1,0  
}}*/


/////////////////

for(i=0;i<M;i++){	
if( i%4 == 0){//i= 0 4 

for(j1=0;j1<2;j1++){
for(i1 = 0; i1< blocksize; i1++) {
extra[j1][i1]=*(fdata[i+2+j1] +2*blocksize+ i1);}}

for(j1=0;j1<2;j1++){
galois_w8_region_xor((fdata[i+2+j1]+2*blocksize),(fdata[i+j1] + 3*blocksize),blocksize);}

for(j1=0;j1<2;j1++){


galois_w08_region_multiply((fdata[i+j1] + 3*blocksize), galois_single_divide(1,e1[1],w), blocksize, (fdata[i+j1] + 3*blocksize), 0);}


for(j1=0;j1<2;j1++){

galois_w08_region_multiply((fdata[i+j1] + 3*blocksize), e[1], blocksize, (fdata[i+2+j1]+2*blocksize), 0);}


for(j1=0;j1<2;j1++){
galois_w8_region_xor(extra[j1],(fdata[i+2+j1]+2*blocksize),blocksize);}//a 1,0  
}}

///////////////////////////
for(i=0;i<M;i++){	
if( i%4 == 0){//i= 0 4 

for(j1=0;j1<2;j1++){
for(i1 = 0; i1< blocksize; i1++) {
extra[j1][i1]=*(fdata[i+2+j1] +4*blocksize+ i1);}}

for(j1=0;j1<2;j1++){
galois_w8_region_xor((fdata[i+2+j1]+4*blocksize),(fdata[i+j1] + 5*blocksize),blocksize);}

for(j1=0;j1<2;j1++){


galois_w08_region_multiply((fdata[i+j1] + 5*blocksize), galois_single_divide(1,e1[2],w), blocksize, (fdata[i+j1] + 5*blocksize), 0);}


for(j1=0;j1<2;j1++){

galois_w08_region_multiply((fdata[i+j1] + 5*blocksize), e[2], blocksize, (fdata[i+2+j1]+4*blocksize), 0);}


for(j1=0;j1<2;j1++){
galois_w8_region_xor(extra[j1],(fdata[i+2+j1]+4*blocksize),blocksize);}//a 1,0  
}}	    
 ////////////////////////////////////////////////////////////////////////if( i%4 == 0){//i= 0 4 8 
for(i=0;i<M;i++){
if( i%4 == 0){

for(j1=0;j1<2;j1++){
for(i1 = 0; i1< blocksize; i1++) {
extra[j1][i1]=*(fdata[i+2+j1] +6*blocksize+ i1);}}

for(j1=0;j1<2;j1++){
galois_w8_region_xor((fdata[i+2+j1]+6*blocksize),(fdata[i+j1] + 7*blocksize),blocksize);}

for(j1=0;j1<2;j1++){

galois_w08_region_multiply((fdata[i+j1] + 7*blocksize), galois_single_divide(1,e1[3],w), blocksize, (fdata[i+j1] + 7*blocksize), 0);}

for(j1=0;j1<2;j1++){

galois_w08_region_multiply((fdata[i+j1] + 7*blocksize), e[3], blocksize, (fdata[i+2+j1]+6*blocksize), 0);}//}

for(j1=0;j1<2;j1++){
galois_w8_region_xor(extra[j1],(fdata[i+2+j1]+6*blocksize),blocksize);}//a 1,0  
}}   
/////////////////////////////////////////////
for(i=0;i<M;i++){	
if( i%8 == 0){

for(j1=0;j1<4;j1++){
for(i1 = 0; i1< blocksize; i1++) {
extra[j1][i1]=*(fdata[i+4+j1] +8*blocksize+ i1);}}

for(j1=0;j1<4;j1++){
galois_w8_region_xor((fdata[i+4+j1]+8*blocksize),(fdata[i+j1] + 9*blocksize),blocksize);}

for(j1=0;j1<4;j1++){

galois_w08_region_multiply((fdata[i+j1] + 9*blocksize), galois_single_divide(1,e1[4],w), blocksize, (fdata[i+j1] + 9*blocksize), 0);}

for(j1=0;j1<4;j1++){

galois_w08_region_multiply((fdata[i+j1] + 9*blocksize), e[4], blocksize, (fdata[i+4+j1]+8*blocksize), 0);}//}

for(j1=0;j1<4;j1++){
galois_w8_region_xor(extra[j1],(fdata[i+4+j1]+8*blocksize),blocksize);}//a 1,0  
}}
/////////////////////////////////////////////////////////
for(i=0;i<M;i++){	
if( i%8 == 0){

for(j1=0;j1<4;j1++){
for(i1 = 0; i1< blocksize; i1++) {
extra[j1][i1]=*(fcoding[i+4+j1] + i1);}}

for(j1=0;j1<4;j1++){
galois_w8_region_xor((fcoding[i+4+j1]),(fcoding[i+j1] + blocksize),blocksize);}

for(j1=0;j1<4;j1++){

galois_w08_region_multiply((fcoding[i+j1] + blocksize), galois_single_divide(1,e1[5],w), blocksize, (fcoding[i+j1] +blocksize), 0);}

for(j1=0;j1<4;j1++){

galois_w08_region_multiply((fcoding[i+j1] + blocksize), e[5], blocksize, (fcoding[i+4+j1]), 0);}

for(j1=0;j1<4;j1++){
galois_w8_region_xor(extra[j1],(fcoding[i+4+j1]),blocksize);}
}}
////////////////////////////////////////////////////

for(i=0;i<M;i++){	
if( i%8 == 0){

for(j1=0;j1<4;j1++){
for(i1 = 0; i1< blocksize; i1++) {
extra[j1][i1]=*(fcoding[i+4+j1] +2*blocksize+ i1);}}

for(j1=0;j1<4;j1++){
galois_w8_region_xor((fcoding[i+4+j1]+2*blocksize),(fcoding[i+j1] + 3*blocksize),blocksize);}

for(j1=0;j1<4;j1++){

galois_w08_region_multiply((fcoding[i+j1] + 3*blocksize), galois_single_divide(1,e1[6],w), blocksize, (fcoding[i+j1] + 3*blocksize), 0);}

for(j1=0;j1<4;j1++){

galois_w08_region_multiply((fcoding[i+j1] + 3*blocksize), e[6], blocksize, (fcoding[i+4+j1]+2*blocksize), 0);}

for(j1=0;j1<4;j1++){
galois_w8_region_xor(extra[j1],(fcoding[i+4+j1]+2*blocksize),blocksize);}//a 1,0  
}}
//////////////////////////
timing_set(&q2);
printf("\n bit_operation_completed\n");

			printf("\n fdata 4*10: char \n ");
		        for(i1=0;i1<4;i1++){
		        for(j=0;j<10;j++){
			printf(" %d ",fdata[2*i1][j*blocksize]);}
			printf("\n");	}

			printf("\n fcoding 4*4: char \n ");
		        for(i1=0;i1<4;i1++){
		        for(j=0;j<4;j++){
			printf(" %d ",fcoding[2*i1][j*blocksize]);}
			printf("\n");	}
 				

	
		
		
timing_set(&q3);
		int **vandemonde;
		vandemonde = (int **)malloc(sizeof(int*)*4);
		for (i = 0; i < 4; i++) {
		vandemonde[i] = (int *)malloc(sizeof(int)*k);}

		int *Gmatrix1_copy;
		Gmatrix1_copy = (int *)malloc(sizeof(int)*4*k);//yi wei
		





	     

		int *p;
		int *p2group;
		int *p3group;

		p = (int *)malloc(sizeof(int)*k);
		p2group = (int *)malloc(sizeof(int)*k);
		p3group = (int *)malloc(sizeof(int)*k);


		       
memset(p,0,k);
memset(p2group,0,k);
memset(p3group,0,k);


		      for(i=0;i<10;i++)  {p[i]=(int)i+1;}
		       


//p[0]=1;p[1]=147;p[2]=138;p[3]=73;p[4]=93;p[5]=161;p[6]=103;p[7]=58;p[8]=99;p[9]=178;
		        for(i=0;i<10;i++){
		        galois_w08_region_multiply((p+i), (int)p[i], 1, (p2group+i), 0);}
		
			for(i=0;i<10;i++){
		        galois_w08_region_multiply((p2group+i), (int)p[i], 1, (p3group+i), 0);}

		 
		        
		      
		
			for( j=0;j<k;j++){//true
		        vandemonde[0][j]=(int)1;
		        vandemonde[1][j]=(int)p[j];
		        vandemonde[2][j]=(int)p2group[j];
		        vandemonde[3][j]=(int)p3group[j];
		        }


			

			
			
			for(i=0;i<4;i++){
			for(i1=0;i1<10;i1++){
			Gmatrix1_copy[i*10+i1]=vandemonde[i][i1];}}
			
printf("3 \n");
			





timing_set(&q4);








//unsigned char **load;
char **load;
 load = (char **)malloc(sizeof(char*)*m);
 for(j = 0; j < m; j++) {
 load[j] = (char *)malloc(sizeof(char)*k*blocksize);}
//unsigned char **load1;
char **load1;
 load1 = (char **)malloc(sizeof(char*)*m);
 for(j = 0; j < m; j++) {
 load1[j] = (char *)malloc(sizeof(char)*4*blocksize);}





 timing_set(&q5);			
     
                if(erased[0]==1 )      
	        {    
			//printf("\n Gmatrix1_copy 10*10: \n ");
			//jerasure_print_matrix(Gmatrix1_copy,4,k,w);
			
		

printf("\nblocksize complete\n");
char **data11;
data11 = (char **)malloc(sizeof(char*)*4);
for(j = 0; j < 4; j++) {
data11[j] = (char *)malloc(sizeof(char)*blocksize);}
char **data12;
data12 = (char **)malloc(sizeof(char*)*4);
for(j = 0; j < 4; j++) {
data12[j] = (char *)malloc(sizeof(char)*blocksize);}


char **data111;
char **coding111;		
data111 = (char **)malloc(sizeof(char *)*k);
coding111 = (char **)malloc(sizeof(char *)*m);
for(i=0;i<k;i++){
data111[i] = (char *)malloc(sizeof(char)*blocksize);}
for(i=0;i<m;i++){
coding111[i] = (char *)malloc(sizeof(char)*blocksize);}

					for( i=0;i<4;i++){ //i= 0 1 2 3
				        for(j1=2;j1<10;j1++){
					for(i1=0;i1<blocksize;i1++){
						load[i][j1*blocksize+i1]=(char)*(fdata[2*i]+j1*blocksize+i1);}}}//i =0 2 4 6


				        for( i=0;i<4;i++){
					for(j=0;j<4;j++){   
				        for(i1=0;i1<blocksize;i1++){
						load1[i][j*blocksize+i1]=(char)*(fcoding[2*i]+j*blocksize+i1);}}}

			/*printf("\nload1\n");
			for(i=0;i<4;i++){
			for(j=0;j<4;j++){   
			printf(" %d ",load1[i][j*blocksize]);}
			printf("\n");}*/
					/*printf("\nfcoding\n");
					for(i=0;i<4;i++){
					for(j=0;j<2;j++){   
					printf(" %d ",*(fcoding[2*i]+j*blocksize));}
					printf("\n");} */

			/*printf("\nload\n");
			for( i=0;i<4;i++){
			for(j=0;j<10;j++){   
			printf(" %d ",load[i][j*blocksize]);}
			printf("\n");}*/

					



erasures[1]=1;
erasures[2]=-1;


		for(i4=0;i4<m;i4++){

		for(jj=0;jj<4;jj++){		
		coding111[jj] = (load1[i4]+jj*blocksize);}
		for(j=0;j<k;j++){
		data111[j] = (load[i4]+j*blocksize);}


			

	        jerasure_matrix_decode(k, m, w, Gmatrix1_copy, 0, erasures, data111, coding111, blocksize);
		
	

		
	

		}//i4
		for(i4=0;i4<m;i4++){

		for(i1=0;i1<blocksize;i1++){
		data11[i4][i1]=*(load[i4]+i1);}//node0 solved value

			
		for(i1=0;i1<blocksize;i1++){
		data12[i4][i1]=*(load[i4]+blocksize+i1);}//node1 solved value
			
		}	
			/*printf("\nload\n");
			for( i=0;i<4;i++){
			for(j=0;j<10;j++){   
			printf(" %d ",load[i][j*blocksize]);}
			printf("\n");}
			printf("\nload1\n");
			for( i=0;i<4;i++){
			for(j=0;j<4;j++){   
			printf(" %d ",load1[i][j*blocksize]);}
			printf("\n");}

			printf("\ndata11\n");
			for( i=0;i<4;i++){
			  
			printf(" %d ",data11[i][0]);}
			
			printf("\ndata12\n");
			for( i=0;i<4;i++){
			  
			printf(" %d ",data12[i][0]);}*/
			
			
			

/*printf( "eraaed:\n");

for(j1=0;j1<k+m;j1++)
{printf("%d ",erased[j1]);}
printf( " \n");
printf( "erasures:\n");
for(j1=0;j1<k+m;j1++)
{printf("%d ",erasures[j1]);}
printf( " \n");
printf( " end~\n");*/



 			   char **original1;
 			   original1 = (char **)malloc(sizeof(char*)*4);
			   for(j = 0; j < 4; j++) {
			   original1[j] = (char *)malloc(sizeof(char)*blocksize);} 
			  
				
			  for(j=0;j<4;j++){	  	
			   galois_w8_region_xor(data12[j],Eextra[j],blocksize); 
			   galois_w8_region_xor(Eextra[j],Eextra1[j],blocksize);}

			

			for(i=0;i<4;i++){
			for(j=0;j<blocksize;j++){
			original1[i][j]=Eextra[i][j];}}

		

			//node 0
			    for(i=0;i<4;i++){
			     for(i1=0;i1<blocksize;i1++){				
			      fdata[2*i+1][0+i1]=*(original1[i]+i1);//i=1 3 5 7
			      fdata[2*i][0+i1]=*(data11[i]+i1);}}//i = 0 2 4 6

			//node 1
			   for(i=0;i<4;i++){
			     for(i1=0;i1<blocksize;i1++){				
			      
			      fdata[2*i][blocksize+i1]=*(Eextra1[i]+i1);}}//i = 0 2 4 6


   			printf("\n fdata 4*8: char \n ");
		        for(i1=0;i1<8;i1++){
		        for(j=0;j<10;j++){
			printf(" %d ",fdata[i1][j*blocksize]);}
			printf("\n");	}
			








	   }//if eraser
timing_set(&q6);


printf( " \ncomplete \n");

		

		
		/* Create decoded file */
		sprintf(fname, "%s/Coding/%s_decoded%s", curdir, cs1, extension);
		if (n == 1) {
			fp = fopen(fname, "wb");
		}
		else {
			fp = fopen(fname, "ab");
		}
		
		for (i4 = 0; i4 < M; i4++) {
		

			if (total+k*blocksize <= origsize) {
			   
				fwrite(fdata[i4], sizeof(char), k*blocksize, fp);
			        total+= k*blocksize;}
			   
			else {
				
				for (i5 = 0; i5 < k*blocksize; i5++) {
					if (total < origsize) {
						
						fprintf(fp, "%c", fdata[i4][i5]);
						total++;
					}
					else {
						break;
					}
					
				}
			}//else
		}






		n++;
		fclose(fp);

	}//while
	/* Free allocated memory */
	free(cs1);
	free(extension);
	free(fname);
	








	
	/* Stop timing and print time */
		matrix_time = timing_delta(&q3, &q4);//matrix
		bit_operation_time= timing_delta(&q1, &q2);
		save_value_time=timing_delta(&t1,&t2);
		repair_time=timing_delta(&q5, &q6);
		sum_time=bit_operation_time +matrix_time+repair_time+save_value_time;


	
	printf("Decoding (MB/sec): %0.10f\n", (((double) origsize)/1024.0/1024.0)/sum_time);
	
	printf("bit_operation_time (sec): %0.10f\n\n", bit_operation_time);
	printf("save_value_time (sec): %0.10f\n\n", save_value_time );
	printf("repair_time (sec): %0.10f\n\n", repair_time );
	
	printf("sum_time (sec): %0.10f\n\n", sum_time);
	return 0;
}	

void ctrl_bs_handler(int dummy) {
	time_t mytime;
	mytime = time(0);
	fprintf(stderr, "\n%s\n", ctime(&mytime));
	fprintf(stderr, "You just typed ctrl-\\ in decoder.c\n");
	fprintf(stderr, "Total number of read ins = %d\n", readins);
	fprintf(stderr, "Current read in: %d\n", n);
	fprintf(stderr, "Method: %s\n\n", Methods[method]);
	signal(SIGQUIT, ctrl_bs_handler);
}
