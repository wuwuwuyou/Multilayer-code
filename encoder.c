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
 *///
   
/* 

This program takes as input an inputfile, k, m, a coding 
technique, w, and packetsize.  It creates k+m files from 
the original file so that k of these files are parts of 
the original file and m of the files are encoded based on 
the given coding technique. The format of the created files 
is the file name with "_k#" or "_m#" and then the extension.  
(For example, inputfile test.txt would yield file "test_k1.txt".)
*/

#include <assert.h>
#include <time.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <signal.h>
#include <gf_rand.h>
#include <unistd.h>
#include "jerasure.h"
#include "reed_sol.h"
#include "cauchy.h"
#include "liberation.h"
#include "timing.h"

#define N 10
#define M 8

enum Coding_Technique {Reed_Sol_Van, Reed_Sol_R6_Op, Cauchy_Orig, Cauchy_Good, Liberation, Blaum_Roth, Liber8tion, RDP, EVENODD, No_Coding};

char *Methods[N] = {"reed_sol_van", "reed_sol_r6_op", "cauchy_orig", "cauchy_good", "liberation", "blaum_roth", "liber8tion", "no_coding"};

/* Global variables for signal handler */
int readins, n;
enum Coding_Technique method;

/* Function prototypes */
int is_prime(int w);
void ctrl_bs_handler(int dummy);

int jfread(void *ptr, int size, int nmembers, FILE *stream)
{
  if (stream != NULL) return fread(ptr, size, nmembers, stream);

  MOA_Fill_Random_Region(ptr, size);
  return size;
}

static void print_data_and_coding(int k, int m, int w, int size,
	char **data, char **coding)
{
	int i, j, x;
	int n, sp;
//	long l;

	if (k > m) n = k;
	else n = m;
	sp = size * 2 + size / (w / 8) + 8;

	printf("%-*sCoding\n", sp, "Data");
	for (i = 0; i < n; i++) {
		if (i < k) {
			printf("D%-2d:", i);
			for (j = 0; j < size; j += (w / 8)) {
				printf(" ");
				for (x = 0; x < w / 8; x++) {
					printf("%02x", (unsigned char)data[i][j + x]);
				}
			}
			printf("    ");
		}
		else printf("%*s", sp, "");
		if (i < m) {
			printf("C%-2d:", i);
			for (j = 0; j < size; j += (w / 8)) {
				printf(" ");
				for (x = 0; x < w / 8; x++) {
					printf("%02x", (unsigned char)coding[i][j + x]);
				}
			}
		}
		printf("\n");
	}
	printf("\n");
}

int main (int argc, char **argv) {
	FILE *fp, *fp2;				// file pointers
	char *block;				// padding file
	int size, newsize;			// size of file and temp size 
	struct stat status;			// finding file size

	
	enum Coding_Technique tech;		// coding technique (parameter)
	int k, m, w, packetsize;		// parameters
	int buffersize;					// paramter
	int i,j,i1,j1,i2,j2;
	int i22,iii;						// loop control variables
	int blocksize;					// size of k+m files
	int total;
	int extra3;
	int stripe_size;
	
	/* Jerasure Arguments */
	char **data;				
	char **coding;
	char **fdata;				
	char **fcoding;
	
	int *matrix;
	int *bitmatrix;
	int **schedule;
	//char *datacopy1;
	//char *datacopy2;
        char *extra1;
	char *extra2;
       // char *datacopy;
	char **extra;

        char **A;					
        char *A1;
	char *A2;
	char **A3;
	char **AA;
	char **AAA;
	char *e;

	
	/* Creation of file name variables */
	char temp[5];
	char *s1, *s2, *extension;
	char *fname;
	int md;
	char *curdir;
	
	/* Timing variables */
	struct timing t1, t2, t3, t4,q1,q2,q3,q4,q5,q6;

	double tsec;
	double totalsec;
	double encode_time;
	double true_encode_time;
	double bit_operation_time;
	double sum_time;
	double matrix_time;

	struct timing start;

	/* Find buffersize */
	int up, down;


	signal(SIGQUIT, ctrl_bs_handler);

	/* Start timing */
	timing_set(&t1);
	totalsec = 0.0;
	matrix = NULL;
	bitmatrix = NULL;
	schedule = NULL;
	
	/* Error check Arguments*/
	if (argc != 8) {
		fprintf(stderr,  "usage: inputfile k m coding_technique w packetsize buffersize\n");
		fprintf(stderr,  "\nChoose one of the following coding techniques: \nreed_sol_van, \nreed_sol_r6_op, \ncauchy_orig, \ncauchy_good, \nliberation, \nblaum_roth, \nliber8tion");
		fprintf(stderr,  "\n\nPacketsize is ignored for the reed_sol's");
		fprintf(stderr,  "\nBuffersize of 0 means the buffersize is chosen automatically.\n");
		fprintf(stderr,  "\nIf you just want to test speed, use an inputfile of \"-number\" where number is the size of the fake file you want to test.\n\n");
		exit(0);
	}
	/* Conversion of parameters and error checking */	
	if (sscanf(argv[2], "%d", &k) == 0 || k <= 0) {
		fprintf(stderr,  "Invalid value for k\n");
		exit(0);
	}
	if (sscanf(argv[3], "%d", &m) == 0 || m < 0) {
		fprintf(stderr,  "Invalid value for m\n");
		exit(0);
	}
	if (sscanf(argv[5],"%d", &w) == 0 || w <= 0) {
		fprintf(stderr,  "Invalid value for w.\n");
		exit(0);
	}
	if (argc == 6) {
		packetsize = 0;
	}
	else {
		if (sscanf(argv[6], "%d", &packetsize) == 0 || packetsize < 0) {
			fprintf(stderr,  "Invalid value for packetsize.\n");
			exit(0);
		}
	}
	if (argc != 8) {
		buffersize = 0;
	}
	else {
		if (sscanf(argv[7], "%d", &buffersize) == 0 || buffersize < 0) {
			fprintf(stderr, "Invalid value for buffersize\n");
			exit(0);
		}
		
	}

	/* Determine proper buffersize by finding the closest valid buffersize to the input value  */
	if (buffersize != 0) {
		if (packetsize != 0 && buffersize%(sizeof(long)*w*k*packetsize) != 0) { 
			up = buffersize;
			down = buffersize;
			while (up%(sizeof(long)*w*k*packetsize) != 0 && (down%(sizeof(long)*w*k*packetsize) != 0)) {
				up++;
				if (down == 0) {
					down--;
				}
			}
			if (up%(sizeof(long)*w*k*packetsize) == 0) {
				buffersize = up;
			}
			else {
				if (down != 0) {
					buffersize = down;
				}
			}
		}
		else if (packetsize == 0 && buffersize%(sizeof(long)*w*k) != 0) {
			up = buffersize;
			down = buffersize;
			while (up%(sizeof(long)*w*k) != 0 && down%(sizeof(long)*w*k) != 0) {
				up++;
				down--;
			}
			if (up%(sizeof(long)*w*k) == 0) {
				buffersize = up;
			}
			else {
				buffersize = down;
			}
		}
	}

	/* Setting of coding technique and error checking */
	
	if (strcmp(argv[4], "no_coding") == 0) {
		tech = No_Coding;
	}
	else if (strcmp(argv[4], "reed_sol_van") == 0) {
		tech = Reed_Sol_Van;
		if (w != 8 && w != 16 && w != 32) {
			fprintf(stderr,  "w must be one of {8, 16, 32}\n");
			exit(0);
		}
	}
	else if (strcmp(argv[4], "reed_sol_r6_op") == 0) {
		if (m != 2) {
			fprintf(stderr,  "m must be equal to 2\n");
			exit(0);
		}
		if (w != 8 && w != 16 && w != 32) {
			fprintf(stderr,  "w must be one of {8, 16, 32}\n");
			exit(0);
		}
		tech = Reed_Sol_R6_Op;
	}
	else if (strcmp(argv[4], "cauchy_orig") == 0) {
		tech = Cauchy_Orig;
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
	}
	else if (strcmp(argv[4], "cauchy_good") == 0) {
		tech = Cauchy_Good;
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
	}
	else if (strcmp(argv[4], "liberation") == 0) {
		if (k > w) {
			fprintf(stderr,  "k must be less than or equal to w\n");
			exit(0);
		}
		if (w <= 2 || !(w%2) || !is_prime(w)) {
			fprintf(stderr,  "w must be greater than two and w must be prime\n");
			exit(0);
		}
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
		if ((packetsize%(sizeof(long))) != 0) {
			fprintf(stderr,  "packetsize must be a multiple of sizeof(long)\n");
			exit(0);
		}
		tech = Liberation;
	}
	else if (strcmp(argv[4], "blaum_roth") == 0) {
		if (k > w) {
			fprintf(stderr,  "k must be less than or equal to w\n");
			exit(0);
		}
		if (w <= 2 || !((w+1)%2) || !is_prime(w+1)) {
			fprintf(stderr,  "w must be greater than two and w+1 must be prime\n");
			exit(0);
		}
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
		if ((packetsize%(sizeof(long))) != 0) {
			fprintf(stderr,  "packetsize must be a multiple of sizeof(long)\n");
			exit(0);
		}
		tech = Blaum_Roth;
	}
	else if (strcmp(argv[4], "liber8tion") == 0) {
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize\n");
			exit(0);
		}
		if (w != 8) {
			fprintf(stderr, "w must equal 8\n");
			exit(0);
		}
		if (m != 2) {
			fprintf(stderr, "m must equal 2\n");
			exit(0);
		}
		if (k > w) {
			fprintf(stderr, "k must be less than or equal to w\n");
			exit(0);
		}
		tech = Liber8tion;
	}
	else {
		fprintf(stderr,  "Not a valid coding technique. Choose one of the following: reed_sol_van, reed_sol_r6_op, cauchy_orig, cauchy_good, liberation, blaum_roth, liber8tion, no_coding\n");
		exit(0);
	}

	/* Set global variable method for signal handler */
	method = tech;

	/* Get current working directory for construction of file names */
	curdir = (char*)malloc(sizeof(char)*1000);	
	assert(curdir == getcwd(curdir, 1000));

        if (argv[1][0] != '-') {

		/* Open file and error check */
		fp = fopen(argv[1], "rb");
		if (fp == NULL) {
			fprintf(stderr,  "Unable to open file.\n");
			exit(0);
		}
	
		/* Create Coding directory */
		i = mkdir("Coding", S_IRWXU);
		if (i == -1 && errno != EEXIST) {
			fprintf(stderr, "Unable to create Coding directory.\n");
			exit(0);
		}
	
		/* Determine original size of file */
		stat(argv[1], &status);	
		size = status.st_size;
        } else {
        	if (sscanf(argv[1]+1, "%d", &size) != 1 || size <= 0) {
                	fprintf(stderr, "Files starting with '-' should be sizes for randomly created input\n");
			exit(1);
		}
        	fp = NULL;
		MOA_Seed(time(0));
        }

	newsize = size;
	
	/* Find new size by determining next closest multiple */
	if (packetsize != 0) {
		if (size%(k*w*packetsize*sizeof(long)) != 0) {
			while (newsize%(k*w*packetsize*sizeof(long)) != 0) 
				newsize++;
		}
	}
	else {
		if (size%(k*w*sizeof(long)) != 0) {
			while (newsize%(k*w*sizeof(long)) != 0) 
				newsize++;
		}
	}
	
	if (buffersize != 0) {
		while (newsize%buffersize != 0) {
			newsize++;
		}
	}


	/* Determine size of k+m files */
	stripe_size=newsize/M;
	blocksize = stripe_size/k;
	
	
	/* Allow for buffersize and determine number of read-ins */
	if (size > buffersize && buffersize != 0) {
		if (newsize%buffersize != 0) {
			readins = newsize/buffersize;
		}
		else {
			readins = newsize/buffersize;
		}
		block = (char *)malloc(sizeof(char)*buffersize);
		blocksize = buffersize/k;
	}
	else {
		readins = 1;
		buffersize = size;
		block = (char *)malloc(sizeof(char)*newsize);
	}
	printf("buffersize:%d\n", buffersize);
	printf("size:%d\n", size);
        printf("newsize:%d\n",newsize);
	printf("stripe_size:%d\n",stripe_size);	
	printf("blocksize:%d\n", blocksize);
	/* Break inputfile name into the filename and extension */	
	s1 = (char*)malloc(sizeof(char)*(strlen(argv[1])+20));
	s2 = strrchr(argv[1], '/');
	if (s2 != NULL) {
		s2++;
		strcpy(s1, s2);
	}
	else {
		strcpy(s1, argv[1]);
	}
	s2 = strchr(s1, '.');
	if (s2 != NULL) {
          extension = strdup(s2);
          *s2 = '\0';
	} else {
          extension = strdup("");
        }
	
	/* Allocate for full file name */
	fname = (char*)malloc(sizeof(char)*(strlen(argv[1])+strlen(curdir)+20));
	sprintf(temp, "%d", k);
	md = strlen(temp);
	
	/* Allocate data and coding */
	data = (char **)malloc(sizeof(char*)*k);
	coding = (char **)malloc(sizeof(char*)*m);
	for (i = 0; i < m; i++) {
		coding[i] = (char *)malloc(sizeof(char)*blocksize);
                if (coding[i] == NULL) { perror("malloc"); exit(1); }
	}
	e = (char *)malloc(sizeof(char)*7);
	fdata = (char **)malloc(sizeof(char*)*M);
	fcoding = (char **)malloc(sizeof(char*)*M);
	
        extra1 = (char *)malloc(sizeof(char)*blocksize);
	extra2 = (char *)malloc(sizeof(char)*blocksize);
        extra = (char **)malloc(sizeof(char*)*128);
		for(i=0;i<128;i++)
		{extra[i] = (char *)malloc(sizeof(char)*blocksize);}


//---------------------------------------------------------------------------
timing_set(&q5);
		unsigned char *p;
		unsigned char *p2group;
		unsigned char *p3group;
		int **vandemonde1;
		int *vandemonde11;
		p = (char *)malloc(sizeof(char)*10);
		p2group = (char *)malloc(sizeof(char)*10);
		p3group = (char *)malloc(sizeof(char)*10);
		vandemonde1 = (int **)malloc(sizeof(int*)*4);
		for (i = 0; i < 4; i++) {
		vandemonde1[i] = (int *)malloc(sizeof(int)*k);}
		vandemonde11 = (int *)malloc(sizeof(int)*4*k);
//------------------------------------------------------------------
		/*unsigned char *p;
		unsigned char *p2group;
		unsigned char *p3group;
		unsigned char *p4group;
		unsigned char *p5group;
		unsigned char *p6group;
		unsigned char *p7group;
		unsigned char *p8group;
		unsigned char *p9group;
		unsigned char *p10group;
		unsigned char *p11group;
		unsigned char *p12group;
		unsigned char *p13group;
		unsigned char *p14group;
		unsigned char *p15group;
	

		p = (char *)malloc(sizeof(char)*16);
		p2group = (char *)malloc(sizeof(char)*16);
		p3group = (char *)malloc(sizeof(char)*16);
		p4group = (char *)malloc(sizeof(char)*16);
		p5group = (char *)malloc(sizeof(char)*16);
		p6group = (char *)malloc(sizeof(char)*16);
		p7group = (char *)malloc(sizeof(char)*16);
		p8group = (char *)malloc(sizeof(char)*16);
		p9group = (char *)malloc(sizeof(char)*16);
		p10group = (char *)malloc(sizeof(char)*16);
		p11group = (char *)malloc(sizeof(char)*16);
		p12group = (char *)malloc(sizeof(char)*16);
		p13group = (char *)malloc(sizeof(char)*16);
		p14group = (char *)malloc(sizeof(char)*16);
		p15group = (char *)malloc(sizeof(char)*16);
	

		unsigned char *mark31;
		unsigned char *mark32;
		unsigned char *mark33;
		unsigned char *mark34;
	        mark31 = (char *)malloc(sizeof(char)*16);
	        mark32 = (char *)malloc(sizeof(char)*16);
	        mark33 = (char *)malloc(sizeof(char)*16);
	        mark34 = (char *)malloc(sizeof(char)*16);*/

//memset(pp, 0, 16);
//  assert(a.cols == b.rows);  mudishixiangdeng



			//for(i=0;i<4;i++){
			//for(i1=0;i1<10;i1++){
			//vandemonde11[i*10+i1]=0;}}
 		 

      

//p2group[10]=121;p2group[11]=144;p2group[12]=169;p2group[13]=196;p2group[14]=225;p2group[15]=27;		
//p3group[0]=1;p3group[1]=8;p3group[2]=27;p3group[3]=64;p3group[4]=125;p3group[5]=-40;p3group[6]=-105;p3group[7]=58;p3group[8]=-29;p3group[9]=-49;

		        for(i=0;i<10;i++)  {p[i]=i+1;}
		        for(i=0;i<10;i++){
		        galois_w08_region_multiply((p+i), (int)p[i], 1, (p2group+i), 0);}
			for(i=0;i<10;i++){
		        galois_w08_region_multiply((p2group+i), (int)p[i], 1, (p3group+i), 0);}	

			/*for(i=0;i<16;i++){
		        galois_w08_region_multiply((p3group+i), (int)p[i], 1, (p4group+i), 0);}
			for(i=0;i<16;i++){
		         galois_w08_region_multiply((p4group+i), (int)p[i], 1, (p5group+i), 0);}

			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p5group+i), (int)p[i], 1, (p6group+i), 0);}

			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p6group+i), (int)p[i], 1, (p7group+i), 0);}

			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p7group+i), (int)p[i], 1, (p8group+i), 0);}

			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p8group+i), (int)p[i], 1, (p9group+i), 0);}

			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p9group+i), (int)p[i], 1, (p10group+i), 0);}
			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p10group+i), (int)p[i], 1, (p11group+i), 0);}

			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p11group+i), (int)p[i], 1, (p12group+i), 0);}
 
			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p12group+i), (int)p[i], 1, (p13group+i), 0);}
			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p13group+i), (int)p[i], 1, (p14group+i), 0);}
			for(i=0;i<16;i++){
		        galois_w08_region_multiply((p14group+i), (int)p[i], 1, (p15group+i), 0);}*/


//-----------------------------------------------------------------  
/*printf(" fan:p\n");
for(i1=0;i1<k;i1++){
		       printf(" %d ",p[i1]);}
			printf(" \n");
for(i1=0;i1<k;i1++){
		       printf(" %d ",p2group[i1]);}
			printf(" \n");
for(i1=0;i1<k;i1++){
		       printf(" %d ",p3group[i1]);}
			printf(" \n");*/
/*for(i1=0;i1<16;i1++){
		       printf(" %d ",p4group[i1]);}
			printf(" \n");

for(i1=0;i1<16;i1++){
		       printf(" %d ",p5group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p6group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p7group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p8group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p9group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p10group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p11group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p12group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p13group[i1]);}
			printf(" \n");

for(i1=0;i1<16;i1++){
		       printf(" %d ",p14group[i1]);}
			printf(" \n");
for(i1=0;i1<16;i1++){
		       printf(" %d ",p15group[i1]);}
			printf(" \n");*/

//-------------------------------------------------------
/*printf(" %d\n",*(p5group));
printf(" %d\n",*(p6group));
printf("begin\n");	
	
galois_w08_region_multiply((p5group),2,1,(p5group) , 0);
galois_w08_region_multiply((p6group),2,1,(p6group) , 0);
printf("begin\n");
printf(" %d\n",*(p5group));
printf(" %d\n",*(p6group));
printf("XOR\n");
printf(" %d\n",*(p));
printf(" %d\n",*(p+2));
galois_w8_region_xor((p), (p+2),1);
printf(" %d\n",*(p+2));*/
//========================================================================

/*printf("begin\n");	
	
printf("begin1\n");
int *mark0;
  mark0= (int *)malloc(sizeof(int)*1);
  mark0[0]=1;

//printf("%d ",mark0[0]);
for(i=0;i<16;i++){
mark31[i]=1;}

for(i=0;i<16;i++){
mark32[i]=p[i];	}
for(i=0;i<16;i++){
mark33[i]=p2group[i];}

for(i=0;i<16;i++){
mark34[i]=p3group[i];}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((mark0), (mark34),1);
	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");	
//---------------------------------------------------
printf("begin2\n");
for(i=0;i<16;i++){
//p[1]=mark31[i];}
mark31[i]=p[1];}


for(i=0;i<16;i++){
galois_w08_region_multiply((p+i),(int) p[2],1, (mark32+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p2group+i), (int)p[3],1, (mark33+i), 0);	}

for(i=0;i<16;i++){
galois_w08_region_multiply((p3group+i), (int)p[4],1, (mark34+i), 0);	}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((p), (mark34+1),1);
	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");	
//------------------------------------------------
printf("begin3\n");
for(i=0;i<16;i++){
galois_w08_region_multiply((p4group+i),(int) p2group[1],1, (mark31+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p5group+i), (int)p2group[2],1, (mark32+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p6group+i),(int) p2group[3],1, (mark33+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p7group+i), (int)p2group[4],1, (mark34+i), 0);	}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((p2group), (mark34+2),1);
	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");

//-----------------------------------------------------------
printf("begin4\n");
		
for(i=0;i<16;i++){
galois_w08_region_multiply((p4group+i),(int) p3group[1],1, (mark31+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p5group+i), (int)p3group[2],1, (mark32+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p6group+i),(int) p3group[3],1, (mark33+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p7group+i), (int)p3group[4],1, (mark34+i), 0);	}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((p3group), (mark34+3),1);
	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");



//-----------------------------------------------
	printf("begin5\n");

for(i=0;i<16;i++){
galois_w08_region_multiply((p8group+i),(int) p4group[1],1, (mark31+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p9group+i), (int)p4group[2],1, (mark32+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p10group+i),(int) p4group[3],1, (mark33+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p11group+i), (int)p4group[4],1, (mark34+i), 0);	}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((p4group), (mark34),1);
galois_w8_region_xor((p4group), (mark34+2),1);	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");


//-----------------------------------------------------------
	printf("begin6\n");

		int *mark;
		
	        mark = (int *)malloc(sizeof(int)*1);
for(i=0;i<16;i++){
galois_w08_region_multiply((p8group+i),(int) p5group[1],1, (mark31+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p9group+i), (int)p5group[2],1, (mark32+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p10group+i),(int) p5group[3],1, (mark33+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p11group+i), (int)p5group[4],1, (mark34+i), 0);	}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((p5group), (mark34+3),1);

galois_w08_region_multiply((p5group),2,1, (mark), 0);
galois_w8_region_xor((mark), (mark34),1);	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");		        
//-----------------------------------------------------------------

	printf("begin7\n");

for(i=0;i<16;i++){
galois_w08_region_multiply((p12group+i),(int) p6group[1],1, (mark31+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p13group+i), (int)p6group[2],1, (mark32+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p14group+i),(int) p6group[3],1, (mark33+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p15group+i), (int)p6group[4],1, (mark34+i), 0);	}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((p6group), (mark34+2),1);

galois_w08_region_multiply((p6group),2,1, (mark), 0);
galois_w8_region_xor((mark), (mark34),1);	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");	



//-----------------------------------------------------------------

	printf("begin8\n");

for(i=0;i<16;i++){
galois_w08_region_multiply((p12group+i),(int) p7group[1],1, (mark31+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p13group+i), (int)p7group[2],1, (mark32+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p14group+i),(int) p7group[3],1, (mark33+i), 0);	}
for(i=0;i<16;i++){
galois_w08_region_multiply((p15group+i), (int)p7group[4],1, (mark34+i), 0);	}


galois_w8_region_xor((mark31), (mark32),16);
galois_w8_region_xor((mark32), (mark33),16);
galois_w8_region_xor((mark33), (mark34),16);
	
galois_w8_region_xor((p7group), (mark34+1),1);
galois_w8_region_xor((p7group), (mark34+3),1);
	
for(i=0;i<16;i++){
printf(" %d ",*(mark34+i));}

printf(" \n");	*/


//-===============================================================================
		    
			
			for( j=0;j<k;j++){//true
		        vandemonde1[0][j]=(int)1;
		        vandemonde1[1][j]=(int)p[j];
		        vandemonde1[2][j]=(int)p2group[j];
		        vandemonde1[3][j]=(int)p3group[j];
		        }


			/*printf("vandemonde 1 matrix: \n");
			jerasure_print_matrix(vandemonde1,k,m,w);


			printf("vandemonde1  erwei wei: \n");
			for(i=0;i<4;i++){
			for(i1=0;i1<10;i1++){
		        printf(" %d ",vandemonde1[i][i1]);}
			printf(" \n");}*/
			
			for(i=0;i<4;i++){
			for(i1=0;i1<10;i1++){
			vandemonde11[i*10+i1]=vandemonde1[i][i1];}}
			
printf("3 \n");
			


		/*printf("\nvandemonde11  yi wei\n: \n");
		printf(" \n");
		    for(i=0;i<m;i++){
			for(i1=0;i1<k;i1++){
		printf(" %d ",vandemonde11[i*k+i1]);}
		printf(" \n");}*/
//------------------------------------------------------------
	/* Create coding matrix or bitmatrix and schedule */
	
		switch(tech) {
		case No_Coding:
			break;
		case Reed_Sol_Van:
			//matrix = reed_sol_vandermonde_coding_matrix(k, m, w);
			matrix=vandemonde11;
			break;
		case Reed_Sol_R6_Op:
			break;
		case Cauchy_Orig:
			matrix = cauchy_original_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case Cauchy_Good:
			matrix = cauchy_good_general_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;	
		case Liberation:
			bitmatrix = liberation_coding_bitmatrix(k, w);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case Blaum_Roth:
			bitmatrix = blaum_roth_coding_bitmatrix(k, w);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case Liber8tion:
			bitmatrix = liber8tion_coding_bitmatrix(k);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case RDP:
		case EVENODD:
			assert(0);
	}

	

	//timing_set(&start);
	timing_set(&q6);
	//totalsec += timing_delta(&t3, &t4);
        printf("matrix: \n");
	jerasure_print_matrix(matrix,k+m,k,w);
/*printf(" \n");
printf(" \n");
for(i=0;i<m;i++){
for(j=0;j<k;j++){
printf(" %d ",matrix[i*k+j]);}
printf(" \n");}

printf("vandemonde 11 matrix: \n");
jerasure_print_matrix(vandemonde11,k+m,k,w);*/




/*
for(i=0;i<k;i++){
for(j=0;j<m;j++){
printf(" %d ",matrix[i*m+j]);}
printf(" \n");}*/


printf("\n");

	/* Read in data until finished */
	n = 1;
	total = 0;

	while (n <= readins) {
		/* Check if padding is needed, if so, add appropriate 
		   number of zeros */
		if (total < size && total+buffersize <= size) {
			total += jfread(block, sizeof(char), buffersize, fp);
		}
		else if (total < size && total+buffersize > size) {
			extra3 = jfread(block, sizeof(char), buffersize, fp);
			for (i = extra3; i < buffersize; i++) {
				block[i] = '0';
			}
		}
		else if (total == size) {
			for (i = 0; i < buffersize; i++) {
				block[i] = '0';
			}
		}

printf("mul-encoding: \n");


timing_set(&q1);
		for(j = 0; j < M; j++)
	     {
		fdata[j] = (char *)malloc(sizeof(char)*k*blocksize);
		fcoding[j] = (char *)malloc(sizeof(char)*m*blocksize);
		/* Set pointers to point to file data */
		for (i = 0; i < k; i++) {
		   data[i] = block+((j*k+i)*blocksize);}
		

              
		
		/* Encode according to coding method */
		switch(tech) {	
			case No_Coding:
				break;
			case Reed_Sol_Van:
				jerasure_matrix_encode(k, m, w, matrix, data, coding, blocksize);
				break;
			case Reed_Sol_R6_Op:
				reed_sol_r6_encode(k, w, data, coding, blocksize);
				break;
			case Cauchy_Orig:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Cauchy_Good:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Liberation:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Blaum_Roth:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Liber8tion:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case RDP:
			case EVENODD:
				assert(0);
		}
 	        
 
			
		/*for(iii=0;iii<m;iii++){-wrong
               for(i1=0;i1<blocksize;i1++){
                   fcoding[j][iii*blocksize+i1]=coding[iii][i1];}
               }*/	


				
				for(iii=0;iii<m;iii++){
				for (i=0;i<blocksize;i++){
				fcoding[j][i22]= *(coding[iii]+i);
				i22++;}}
				i22=0;
				
				 //for(i=0;i<k*blocksize;i++)-wrong
				  //{
				 // fdata[j][i] = *(block+j*k*blocksize+i);}

				for(iii=0;iii<k;iii++){
				for (i=0;i<blocksize;i++){
				fdata[j][i22]= *(data[iii]+i);
				i22++;}}
				i22=0;



	   
		
	   }		
timing_set(&q2);

printf("encoder complete \n");		
	
printf( " after operation fdata first strip  :\n");
	  		
	


			printf("\n fdata 4*10: char 0 2 4 6  \n ");
		        for(i1=0;i1<4;i1++){
		        for(j=0;j<10;j++){
			printf(" %d ",fdata[2*i1][j*blocksize]);}
			printf("\n");	}

			printf("\n fcoding 4*2: char 0 2 4 6 \n ");
		        for(i1=0;i1<4;i1++){
		        for(j=0;j<4;j++){
			printf(" %d ",fcoding[2*i1][j*blocksize]);}
			printf("\n");	}
 				
			printf("\n fdata 4*10: char 1 3 5 7  \n ");
		        for(i1=0;i1<4;i1++){
		        for(j=0;j<10;j++){
			printf(" %d ",fdata[2*i1+1][j*blocksize]);}
			printf("\n");	}	
				

printf(" bit_operation_start:\n");		
 timing_set(&q3);       

	
        for(i=0;i<7;i++){
               e[0]=20; e[1]=18;e[2]=21;e[3]=16;e[4]=25;e[5]=13;e[6]=54;}
    
   
 printf("0\n");

	for(i=0;i<M;i++){
           if( i%2 == 0){//i =0,2,4,6
		for (i1=0;i1<blocksize;i1++){
			extra1[i1]=*(fdata[i] +blocksize+ i1);
			extra2[i1]=*(fdata[i+1] + i1);}

	
		galois_region_xor(fdata[i+1],(fdata[i] + blocksize),blocksize);

	
		galois_w08_region_multiply(extra1, e[0], blocksize, fdata[i+1], 0);

		galois_w8_region_xor(extra2, (fdata[i+1]), blocksize);}}

        for(i=0;i<M;i++){
	   if( i%4 == 0 ){///i=0,4
               	
		for(j=0;j<2;j++){ //j=0,1
		for (i1=0;i1<blocksize;i1++){
		extra[j][i1]= *(fdata[i+j]+3*blocksize+i1);}}                   
		    for(j=2;j<4;j++){//j=2,3
		    for (i1=0;i1<blocksize;i1++){
                extra[j][i1] = *(fdata[i+j]+2*blocksize+i1);}}



 		    for(j=0;j<2;j++){

	 	 galois_w8_region_xor((extra[j+2]), (fdata[i+j]  + 3*blocksize),blocksize);}

		
		    for(j=2;j<4;j++){
	         galois_w08_region_multiply(extra[j-2], e[1], blocksize, (fdata[i+j]+2*blocksize), 0);}
	    
		
		    for(j=2;j<4;j++){
	
		 galois_w8_region_xor(extra[j], (fdata[i+j]  + 2*blocksize),blocksize);}}}
 printf("2\n");

	for(i=0;i<M;i++){
	   if( i%4 == 0 ){///i=0,4
               	
		for(j=0;j<2;j++){ //j=0,1
		for (i1=0;i1<blocksize;i1++){
		extra[j][i1]= *(fdata[i+j]+5*blocksize+i1);}}                   
		    for(j=2;j<4;j++){//j=2,3
		    for (i1=0;i1<blocksize;i1++){
                extra[j][i1] = *(fdata[i+j]+4*blocksize+i1);}}



 		    for(j=0;j<2;j++){

	 	 galois_w8_region_xor((extra[j+2]), (fdata[i+j]  + 5*blocksize),blocksize);}

		
		    for(j=2;j<4;j++){
	         galois_w08_region_multiply(extra[j-2], e[2], blocksize, (fdata[i+j]+4*blocksize), 0);}
	    
		
		    for(j=2;j<4;j++){
	
		 galois_w8_region_xor(extra[j], (fdata[i+j]  + 4*blocksize),blocksize);}}}


 printf("3\n");

	for(i=0;i<M;i++){
	   if( i%4 == 0 ){///i=0,4
               	
		for(j=0;j<2;j++){ //j=0,1
		for (i1=0;i1<blocksize;i1++){
		extra[j][i1]= *(fdata[i+j]+7*blocksize+i1);}}                   
		    for(j=2;j<4;j++){//j=2,3
		    for (i1=0;i1<blocksize;i1++){
                extra[j][i1] = *(fdata[i+j]+6*blocksize+i1);}}



 		    for(j=0;j<2;j++){

	 	 galois_w8_region_xor((extra[j+2]), (fdata[i+j]  + 7*blocksize),blocksize);}

		
		    for(j=2;j<4;j++){
	         galois_w08_region_multiply(extra[j-2], e[3], blocksize, (fdata[i+j]+6*blocksize), 0);}
	    
		
		    for(j=2;j<4;j++){
	
		 galois_w8_region_xor(extra[j], (fdata[i+j]  + 6*blocksize),blocksize);}}}

 printf("4\n");

for(i=0;i<M;i++){
	 if( i%8 == 0 ){//i = 0,8,16,32,40,48,56,64,72,80,88,96,104,112,120
		int t4=8;
     

                for(j=0;j<t4/2;j++){
		for (i1=0;i1<blocksize;i1++){
		extra[j][i1]= *(fdata[i+j]+9*blocksize+i1);}}                   
		    for(j=t4/2;j<t4;j++){
		    for (i1=0;i1<blocksize;i1++){
                extra[j][i1] = *(fdata[i+j]+8*blocksize+i1);}}


 		    for(j=0;j<t4/2;j++){
		galois_w8_region_xor((extra[j+4]), (fdata[i+j]  + 9*blocksize),blocksize);}
		
		    for(j=t4/2;j<t4;j++){
		galois_w08_region_multiply(extra[j-4], e[4], blocksize, (fdata[i+j]+8*blocksize), 0);}

		   
		    for(j=t4/2;j<t4;j++){
		
		 galois_w8_region_xor(extra[j], (fdata[i+j]  + 8*blocksize),blocksize);}}}


 printf("5\n");

for(i=0;i<M;i++){
	 if( i%8 == 0 ){//i = 0
		int t4=8;
     

                for(j=0;j<t4/2;j++){
		for (i1=0;i1<blocksize;i1++){
		extra[j][i1]= *(fcoding[i+j]+blocksize+i1);}}                   
		    for(j=t4/2;j<t4;j++){
		    for (i1=0;i1<blocksize;i1++){
                extra[j][i1] = *(fcoding[i+j]+i1);}}


 		    for(j=0;j<t4/2;j++){
		galois_w8_region_xor((extra[j+4]), (fcoding[i+j]  + blocksize),blocksize);}
		
		    for(j=t4/2;j<t4;j++){
		galois_w08_region_multiply(extra[j-4], e[5], blocksize, (fcoding[i+j]), 0);}

		   
		    for(j=t4/2;j<t4;j++){
		
		 galois_w8_region_xor(extra[j], (fcoding[i+j] ),blocksize);}}}
 printf("6\n");

for(i=0;i<M;i++){
	 if( i%8 == 0 ){//i = 0
		int t4=8;
     

                for(j=0;j<t4/2;j++){
		for (i1=0;i1<blocksize;i1++){
		extra[j][i1]= *(fcoding[i+j]+3*blocksize+i1);}}                   
		    for(j=t4/2;j<t4;j++){
		    for (i1=0;i1<blocksize;i1++){
                extra[j][i1] = *(fcoding[i+j]+2*blocksize+i1);}}


 		    for(j=0;j<t4/2;j++){
		galois_w8_region_xor((extra[j+4]), (fcoding[i+j]  + 3*blocksize),blocksize);}
		
		    for(j=t4/2;j<t4;j++){
		galois_w08_region_multiply(extra[j-4], e[6], blocksize, (fcoding[i+j]+ 2*blocksize), 0);}

		   
		    for(j=t4/2;j<t4;j++){
		
		 galois_w8_region_xor(extra[j], (fcoding[i+j]+ 2*blocksize ),blocksize);}}}
     
timing_set(&q4);


printf("bit operation ended \n");
    
			printf("\n fdata 4*10: char \n ");
		        for(i1=0;i1<4;i1++){
		        for(j=0;j<10;j++){
			printf(" %d ",fdata[2*i1][j*blocksize]);}
			printf("\n");	}

			printf("\n fcoding 4*2: char \n ");
		        for(i1=0;i1<4;i1++){
		        for(j=0;j<4;j++){
			printf(" %d ",fcoding[2*i1][j*blocksize]);}
			printf("\n");	}

		/* Write data and encoded data to k+m files */
		for	(i = 0; i < k; i++) {
		 
			if (fp == NULL) {
				bzero(fdata[i], blocksize);
 			} else {
				sprintf(fname, "%s/Coding/%s_k%0*d%s", curdir, s1, md, i, extension);
				if (n == 1) {
					fp2 = fopen(fname, "wb");
				}
				else {
				
				fp2 = fopen(fname, "ab");
				}
				for(j=0;j<M;j++){
				fwrite(&fdata[j][(i)*blocksize], sizeof(char), blocksize, fp2);}
				
				fclose(fp2);
			}
			
		}
             //printf(" outComplete33\n\n");
		for	(i = 0; i < m; i++) {
			if (fp == NULL) {
				bzero(fdata[i], blocksize);
 			} else {
				sprintf(fname, "%s/Coding/%s_m%0*d%s", curdir, s1, md, i, extension);
				//if (n == 1) {
				//	fp2 = fopen(fname, "wb");
				//}
				//else {
					fp2 = fopen(fname, "ab");
				//}
				for(j=0;j<M;j++){
				fwrite(&fcoding[j][(i)*blocksize], sizeof(char), blocksize, fp2);}
				fclose(fp2);
			}
		}
		n++;
		/* Calculate encoding time */

		matrix_time = timing_delta(&q5, &q6);//matrix
		encode_time= timing_delta(&q1, &q2);
		
		bit_operation_time= timing_delta(&q3, &q4);
		sum_time= matrix_time+bit_operation_time+encode_time;
	}

	/* Create metadata file */
        if (fp != NULL) {
		sprintf(fname, "%s/Coding/%s_meta.txt", curdir, s1);
		fp2 = fopen(fname, "wb");
		fprintf(fp2, "%s\n", argv[1]);
		fprintf(fp2, "%d\n", size);
		fprintf(fp2, "%d %d %d %d %d\n", k, m, w, packetsize, buffersize);
		fprintf(fp2, "%s\n", argv[4]);
		fprintf(fp2, "%d\n", tech);
		fprintf(fp2, "%d\n", readins);
		fclose(fp2);
	}


	/* Free allocated memory */
	free(s1);
	free(fname);
	free(block);
	free(curdir);
	
	/* Calculate rate in MB/sec and print */
	timing_set(&t2);
	tsec = timing_delta(&t1, &t2);
	printf("Encoding (MB/sec): %0.10f\n", (((double) size)/1024.0/1024.0)/sum_time);
	
	printf("encode_time (sec): %0.10f\n", encode_time);
	printf("matrix_time (sec): %0.10f\n", matrix_time);
	
	printf("bit_operation_time (sec): %0.10f\n", bit_operation_time);
	printf("sum_time (sec): %0.10f\n", sum_time);
	return 0;
}


/* is_prime returns 1 if number if prime, 0 if not prime */
int is_prime(int w) {
	int prime55[] = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
	    73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,
		    181,191,193,197,199,211,223,227,229,233,239,241,251,257};
	int i;
	for (i = 0; i < 55; i++) {
		if (w%prime55[i] == 0) {
			if (w == prime55[i]) return 1;
			else { return 0; }
		}
	}
	assert(0);
}

/* Handles ctrl-\ event */
void ctrl_bs_handler(int dummy) {
	time_t mytime;
	mytime = time(0);
	fprintf(stderr, "\n%s\n", ctime(&mytime));
	fprintf(stderr, "You just typed ctrl-\\ in encoder.c.\n");
	fprintf(stderr, "Total number of read ins = %d\n", readins);
	fprintf(stderr, "Current read in: %d\n", n);
	fprintf(stderr, "Method: %s\n\n", Methods[method]);	
	signal(SIGQUIT, ctrl_bs_handler);
}



























