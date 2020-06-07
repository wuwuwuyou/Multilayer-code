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

   Revision 2.x - 2014: James S. Plank and Kevin M. Greenan
   Revision 1.2 - 2008: James S. Plank, Scott Simmerman and Catherine D. Schuman.
   Revision 1.0 - 2007: James S. Plank
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>

#include "galois.h"

#define MAX_GF_INSTANCES 64
gf_t *gfp_array[MAX_GF_INSTANCES] = { 0 };
int  gfp_is_composite[MAX_GF_INSTANCES] = { 0 };

gf_t *galois_get_field_ptr(int w)
{
  if (gfp_array[w] != NULL) {
    return gfp_array[w];
  }

  return NULL;
}

gf_t* galois_init_field(int w,
                        int mult_type,
                        int region_type,
                        int divide_type,
                        uint64_t prim_poly,
                        int arg1,
                        int arg2)
{
  int scratch_size;
  void *scratch_memory;
  gf_t *gfp;

  if (w <= 0 || w > 32) {
    fprintf(stderr, "ERROR -- cannot init default Galois field for w=%d\n", w);
    assert(0);
  }

  gfp = (gf_t *) malloc(sizeof(gf_t));
  if (!gfp) {
    fprintf(stderr, "ERROR -- cannot allocate memory for Galois field w=%d\n", w);
    assert(0);
  }

  scratch_size = gf_scratch_size(w, mult_type, region_type, divide_type, arg1, arg2);
  if (!scratch_size) {
    fprintf(stderr, "ERROR -- cannot get scratch size for base field w=%d\n", w);
    assert(0);
  }

  scratch_memory = malloc(scratch_size);
  if (!scratch_memory) {
    fprintf(stderr, "ERROR -- cannot get scratch memory for base field w=%d\n", w);
    assert(0);
  }

  if(!gf_init_hard(gfp,
                   w, 
                   mult_type, 
                   region_type, 
                   divide_type, 
                   prim_poly, 
                   arg1, 
                   arg2, 
                   NULL, 
                   scratch_memory))
  {
    fprintf(stderr, "ERROR -- cannot init default Galois field for w=%d\n", w);
    assert(0);
  }

  gfp_is_composite[w] = 0;
  return gfp;
}

gf_t* galois_init_composite_field(int w,
                                int region_type,
                                int divide_type,
                                int degree,
                                gf_t* base_gf)
{
  int scratch_size;
  void *scratch_memory;
  gf_t *gfp;
  
  if (w <= 0 || w > 32) {
    fprintf(stderr, "ERROR -- cannot init composite field for w=%d\n", w);
    assert(0);
  }
  
  gfp = (gf_t *) malloc(sizeof(gf_t));
  if (!gfp) {
    fprintf(stderr, "ERROR -- cannot allocate memory for Galois field w=%d\n", w);
    assert(0);
  }

  scratch_size = gf_scratch_size(w, GF_MULT_COMPOSITE, region_type, divide_type, degree, 0);
  if (!scratch_size) {
    fprintf(stderr, "ERROR -- cannot get scratch size for composite field w=%d\n", w);
    assert(0);
  }

  scratch_memory = malloc(scratch_size);
  if (!scratch_memory) {
    fprintf(stderr, "ERROR -- cannot get scratch memory for composite field w=%d\n", w);
    assert(0);
  }

  if(!gf_init_hard(gfp,
                   w,
                   GF_MULT_COMPOSITE,
                   region_type,
                   divide_type,
                   0, 
                   degree, 
                   0, 
                   base_gf,
                   scratch_memory))
  {
    fprintf(stderr, "ERROR -- cannot init default composite field for w=%d\n", w);
    assert(0);
  }
  gfp_is_composite[w] = 1;
  return gfp;
}

int galois_init_default_field(int w)
{
  if (gfp_array[w] == NULL) {
    gfp_array[w] = (gf_t*)malloc(sizeof(gf_t));
    if(gfp_array[w] == NULL)
      return ENOMEM;
    if (!gf_init_easy(gfp_array[w], w))
      return EINVAL;
  }
  return 0;
}

int galois_uninit_field(int w)
{
  int ret = 0;
  if (gfp_array[w] != NULL) {
    int recursive = 1;
    ret = gf_free(gfp_array[w], recursive);
    free(gfp_array[w]);
    gfp_array[w] = NULL;
  }
  return ret;
}

static void galois_init(int w)
{
  if (w <= 0 || w > 32) {
    fprintf(stderr, "ERROR -- cannot init default Galois field for w=%d\n", w);
    assert(0);
  }

  switch (galois_init_default_field(w)) {
  case ENOMEM:
    fprintf(stderr, "ERROR -- cannot allocate memory for Galois field w=%d\n", w);
    assert(0);
    break;
  case EINVAL:
    fprintf(stderr, "ERROR -- cannot init default Galois field for w=%d\n", w);
    assert(0);
    break;
  }
}


static int is_valid_gf(gf_t *gf, int w)
{
  // TODO: I assume we may eventually
  // want to do w=64 and 128, so w
  // will be needed to perform this check
  (void)w;

  if (gf == NULL) {
    return 0;
  }
  if (gf->multiply.w32 == NULL) {
    return 0;
  }
  if (gf->multiply_region.w32 == NULL) {
    return 0;
  }
  if (gf->divide.w32 == NULL) {
    return 0;
  }
  if (gf->inverse.w32 == NULL) {
    return 0;
  }
  if (gf->extract_word.w32 == NULL) {
    return 0;
  }

  return 1;
}

void galois_change_technique(gf_t *gf, int w)
{
  if (w <= 0 || w > 32) {
    fprintf(stderr, "ERROR -- cannot support Galois field for w=%d\n", w);
    assert(0);
  }

  if (!is_valid_gf(gf, w)) {
    fprintf(stderr, "ERROR -- overriding with invalid Galois field for w=%d\n", w);
    assert(0);
  }

  if (gfp_array[w] != NULL) {
    gf_free(gfp_array[w], gfp_is_composite[w]);
  }

  gfp_array[w] = gf;
}

int galois_single_multiply(int x, int y, int w)
{
  if (x == 0 || y == 0) return 0;
  
  if (gfp_array[w] == NULL) {
    galois_init(w);
  }

  if (w <= 32) {
    return gfp_array[w]->multiply.w32(gfp_array[w], x, y);
  } else {
    fprintf(stderr, "ERROR -- Galois field not implemented for w=%d\n", w);
    return 0;
  }
}

int galois_single_divide(int x, int y, int w)
{
  if (x == 0) return 0;
  if (y == 0) return -1;

  if (gfp_array[w] == NULL) {
    galois_init(w);
  }

  if (w <= 32) {
    return gfp_array[w]->divide.w32(gfp_array[w], x, y);
  } else {
    fprintf(stderr, "ERROR -- Galois field not implemented for w=%d\n", w);
    return 0;
  }
}

void galois_w08_region_multiply(char *region,      /* Region to multiply */
                                  int multby,       /* Number to multiply by */
                                  int nbytes,        /* Number of bytes in region */
                                  char *r2,          /* If r2 != NULL, products go here */
                                  int add)
{
  if (gfp_array[8] == NULL) {
    galois_init(8);
  }
  gfp_array[8]->multiply_region.w32(gfp_array[8], region, r2, multby, nbytes, add);
}

void galois_w16_region_multiply(char *region,      /* Region to multiply */
                                  int multby,       /* Number to multiply by */
                                  int nbytes,        /* Number of bytes in region */
                                  char *r2,          /* If r2 != NULL, products go here */
                                  int add)
{
  if (gfp_array[16] == NULL) {
    galois_init(16);
  }
  gfp_array[16]->multiply_region.w32(gfp_array[16], region, r2, multby, nbytes, add);
}


void galois_w32_region_multiply(char *region,      /* Region to multiply */
                                  int multby,       /* Number to multiply by */
                                  int nbytes,        /* Number of bytes in region */
                                  char *r2,          /* If r2 != NULL, products go here */
                                  int add)
{
  if (gfp_array[32] == NULL) {
    galois_init(32);
  }
  gfp_array[32]->multiply_region.w32(gfp_array[32], region, r2, multby, nbytes, add);
}

void galois_w8_region_xor(void *src, void *dest, int nbytes)
{
  if (gfp_array[8] == NULL) {
    galois_init(8);
  }
  gfp_array[8]->multiply_region.w32(gfp_array[32], src, dest, 1, nbytes, 1);
}

void galois_w16_region_xor(void *src, void *dest, int nbytes)
{
  if (gfp_array[16] == NULL) {
    galois_init(16);
  }
  gfp_array[16]->multiply_region.w32(gfp_array[16], src, dest, 1, nbytes, 1);
}

void galois_w32_region_xor(void *src, void *dest, int nbytes)
{
  if (gfp_array[32] == NULL) {
    galois_init(32);
  }
  gfp_array[32]->multiply_region.w32(gfp_array[32], src, dest, 1, nbytes, 1);
}



void galois_region_xor(char *src, char *dest, int nbytes)
{
  if (nbytes >= 16) {
    galois_w32_region_xor(src, dest, nbytes);
  } else {
    int i = 0;
    for (i = 0; i < nbytes; i++) {
      *dest ^= *src;
      dest++;
      src++;
    } 
  }
}


int galois_inverse(int y, int w)
{
  if (y == 0) return -1;
  return galois_single_divide(1, y, w);
}






int LOG_TABLE[]= {
            -1,    0,    1,   25,    2,   50,   26,  198,
            3,  223,   51,  238,   27,  104,  199,   75,
            4,  100,  224,   14,   52,  141,  239,  129,
            28,  193,  105,  248,  200,    8,   76,  113,
            5,  138,  101,   47,  225,   36,   15,   33,
            53,  147,  142,  218,  240,   18,  130,   69,
            29,  181,  194,  125,  106,   39,  249,  185,
            201,  154,    9,  120,   77,  228,  114,  166,
            6,  191,  139,   98,  102,  221,   48,  253,
            226,  152,   37,  179,   16,  145,   34,  136,
            54,  208,  148,  206,  143,  150,  219,  189,
            241,  210,   19,   92,  131,   56,   70,   64,
            30,   66,  182,  163,  195,   72,  126,  110,
            107,   58,   40,   84,  250,  133,  186,   61,
            202,   94,  155,  159,   10,   21,  121,   43,
            78,  212,  229,  172,  115,  243,  167,   87,
            7,  112,  192,  247,  140,  128,   99,   13,
            103,   74,  222,  237,   49,  197,  254,   24,
            227,  165,  153,  119,   38,  184,  180,  124,
            17,   68,  146,  217,   35,   32,  137,   46,
            55,   63,  209,   91,  149,  188,  207,  205,
            144,  135,  151,  178,  220,  252,  190,   97,
            242,   86,  211,  171,   20,   42,   93,  158,
            132,   60,   57,   83,   71,  109,   65,  162,
            31,   45,   67,  216,  183,  123,  164,  118,
            196,   23,   73,  236,  127,   12,  111,  246,
            108,  161,   59,   82,   41,  157,   85,  170,
            251,   96,  134,  177,  187,  204,   62,   90,
            203,   89,   95,  176,  156,  169,  160,   81,
            11,  245,   22,  235,  122,  117,   44,  215,
            79,  174,  213,  233,  230,  231,  173,  232,
            116,  214,  244,  234,  168,   80,   88,  175

    };
int EXP_TABLE[] ={
            1,    2,    4,    8,   16,   32,   64, -128,
            29,   58,  116,  -24,  -51, -121,   19,   38,
            76, -104,   45,   90,  -76,  117,  -22,  -55,
            -113,    3,    6,   12,   24,   48,   96,  -64,
            -99,   39,   78, -100,   37,   74, -108,   53,
            106,  -44,  -75,  119,  -18,  -63,  -97,   35,
            70, -116,    5,   10,   20,   40,   80,  -96,
            93,  -70,  105,  -46,  -71,  111,  -34,  -95,
            95,  -66,   97,  -62, -103,   47,   94,  -68,
            101,  -54, -119,   15,   30,   60,  120,  -16,
            -3,  -25,  -45,  -69,  107,  -42,  -79,  127,
            -2,  -31,  -33,  -93,   91,  -74,  113,  -30,
            -39,  -81,   67, -122,   17,   34,   68, -120,
            13,   26,   52,  104,  -48,  -67,  103,  -50,
            -127,   31,   62,  124,   -8,  -19,  -57, -109,
            59,  118,  -20,  -59, -105,   51,  102,  -52,
            -123,   23,   46,   92,  -72,  109,  -38,  -87,
            79,  -98,   33,   66, -124,   21,   42,   84,
            -88,   77, -102,   41,   82,  -92,   85,  -86,
            73, -110,   57,  114,  -28,  -43,  -73,  115,
            -26,  -47,  -65,   99,  -58, -111,   63,  126,
            -4,  -27,  -41,  -77,  123,  -10,  -15,   -1,
            -29,  -37,  -85,   75, -106,   49,   98,  -60,
            -107,   55,  110,  -36,  -91,   87,  -82,   65,
            -126,   25,   50,  100,  -56, -115,    7,   14,
            28,   56,  112,  -32,  -35,  -89,   83,  -90,
            81,  -94,   89,  -78,  121,  -14,   -7,  -17,
            -61, -101,   43,   86,  -84,   69, -118,    9,
            18,   36,   72, -112,   61,  122,  -12,  -11,
            -9,  -13,   -5,  -21,  -53, -117,   11,   22,
            44,   88,  -80,  125,   -6,  -23,  -49, -125,
            27,   54,  108,  -40,  -83,   71, -114,
            // Repeat the table a second time, so multiply()
            // does not have to check bounds.
            1,    2,    4,    8,   16,   32,   64, -128,
            29,   58,  116,  -24,  -51, -121,   19,   38,
            76, -104,   45,   90,  -76,  117,  -22,  -55,
            -113,    3,    6,   12,   24,   48,   96,  -64,
            -99,   39,   78, -100,   37,   74, -108,   53,
            106,  -44,  -75,  119,  -18,  -63,  -97,   35,
            70, -116,    5,   10,   20,   40,   80,  -96,
            93,  -70,  105,  -46,  -71,  111,  -34,  -95,
            95,  -66,   97,  -62, -103,   47,   94,  -68,
            101,  -54, -119,   15,   30,   60,  120,  -16,
            -3,  -25,  -45,  -69,  107,  -42,  -79,  127,
            -2,  -31,  -33,  -93,   91,  -74,  113,  -30,
            -39,  -81,   67, -122,   17,   34,   68, -120,
            13,   26,   52,  104,  -48,  -67,  103,  -50,
            -127,   31,   62,  124,   -8,  -19,  -57, -109,
            59,  118,  -20,  -59, -105,   51,  102,  -52,
            -123,   23,   46,   92,  -72,  109,  -38,  -87,
            79,  -98,   33,   66, -124,   21,   42,   84,
            -88,   77, -102,   41,   82,  -92,   85,  -86,
            73, -110,   57,  114,  -28,  -43,  -73,  115,
            -26,  -47,  -65,   99,  -58, -111,   63,  126,
            -4,  -27,  -41,  -77,  123,  -10,  -15,   -1,
            -29,  -37,  -85,   75, -106,   49,   98,  -60,
            -107,   55,  110,  -36,  -91,   87,  -82,   65,
            -126,   25,   50,  100,  -56, -115,    7,   14,
            28,   56,  112,  -32,  -35,  -89,   83,  -90,
            81,  -94,   89,  -78,  121,  -14,   -7,  -17,
            -61, -101,   43,   86,  -84,   69, -118,    9,
            18,   36,   72, -112,   61,  122,  -12,  -11,
            -9,  -13,   -5,  -21,  -53, -117,   11,   22,
            44,   88,  -80,  125,   -6,  -23,  -49, -125,
            27,   54,  108,  -40,  -83,   71, -114
    };


 char divide(char a, char b) {
        if (a == 0) {
            return 0;
        }
       
        int logA = LOG_TABLE[a & 0xFF];
        int logB = LOG_TABLE[b & 0xFF];
        int logResult = logA - logB;
        if (logResult < 0) {
            logResult += 255;
        }
        return EXP_TABLE[logResult];
    }


void galois_region_xor1(           char *r1,         /* Region 1 */
                                  char *r2,         /* Region 2 */
                                  char *r3,         /* Sum region (r3 = r1 ^ r2) -- can be r1 or r2 */
                                  int nbytes)       /* Number of bytes in region */
{
  long *l1;
  long *l2;
  long *l3;
  long *ltop;
  char *ctop;
  
  ctop = r1 + nbytes;
  ltop = (long *) ctop;
  l1 = (long *) r1;
  l2 = (long *) r2;
  l3 = (long *) r3;
 
  while (l1 < ltop) {
    *l3 = ((*l1)  ^ (*l2));
    l1++;
    l2++;
    l3++;
  }
}



  char multiply(char a, char b) {
        if (a == 0 || b == 0) {
            return 0;
        }
        else {
            int logA = LOG_TABLE[a & 0xFF];
            int logB = LOG_TABLE[b & 0xFF];
            int logResult = logA + logB;
            return EXP_TABLE[logResult];
        }
    }











