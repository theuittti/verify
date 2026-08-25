#pragma once
#define __mm256 float*

extern __mm256 REG;
extern int COUNTER;

/*@
requires COUNTER >= 1;
requires \forall integer i; i > 0 ==> \valid(REG + (0 .. i));
assigns REG[8*COUNTER .. 8*COUNTER + 7];
assigns COUNTER;
ensures \forall integer i; 0 <= i <= 7 ==> \result[i] == 0.0;
ensures \result == REG + \old(COUNTER) * 8;
ensures COUNTER == 1 + \old(COUNTER);
ensures \valid(\result + (0 .. 7));
ensures \valid_read(\result + (0 .. 7));
*/
__mm256 _mm256_setzero_ps(void);

/*@
requires COUNTER >= 1;
requires \forall integer i; i > 0 ==> \valid(REG + (0 .. i));
assigns REG[8*COUNTER .. 8*COUNTER + 7];
assigns COUNTER;
ensures \forall integer i; 0 <= i <= 7 ==> \result[i] == v;
ensures \result == REG + \old(COUNTER) * 8;
ensures COUNTER == 1 + \old(COUNTER);
ensures \valid(\result + (0 .. 7));
ensures \valid_read(\result + (0 .. 7));
*/
__mm256 _mm256_set1_ps(float v);

/*@
requires COUNTER >= 1;
requires \valid_read(a + (0 .. 7));
requires \forall integer i; i > 0 ==> \valid(REG + (0 .. i));
requires \separated(a + (0 .. 7), REG + (8*COUNTER .. 8*COUNTER + 7));
assigns REG[8*COUNTER .. 8*COUNTER + 7];
assigns COUNTER;
ensures \forall integer i; 0 <= i <= 7 ==> \result[i] == a[i];
ensures \result == REG + \old(COUNTER) * 8;
ensures COUNTER == 1 + \old(COUNTER);
ensures \valid(\result + (0 .. 7));
ensures \valid_read(\result + (0 .. 7));
*/
__mm256 _mm256_loadu_ps(const float* a);

/*@
requires \valid(mem_addr + (0 .. 7));
requires \valid_read(a + (0 .. 7));
requires \separated(a + (0 .. 7), mem_addr + (0 .. 7));
assigns mem_addr[0 .. 7];
ensures \forall integer i; 0 <= i <= 7 ==> mem_addr[i] == a[i];
*/
void _mm256_storeu_ps(float* mem_addr, __mm256 a);

/*@
requires \valid_read(a + (0 .. 7));
requires \valid_read(b + (0 .. 7));
requires \valid_read(c + (0 .. 7));
requires COUNTER >= 1;
requires \forall integer i; i > 0 ==> \valid(REG + (0 .. i));
requires \separated(a + (0 .. 7), REG + (8*COUNTER .. 8*COUNTER + 7));
requires \separated(b + (0 .. 7), REG + (8*COUNTER .. 8*COUNTER + 7));
requires \separated(c + (0 .. 7), REG + (8*COUNTER .. 8*COUNTER + 7));
assigns REG[8*COUNTER .. 8*COUNTER + 7];
assigns COUNTER;
ensures \forall integer i; 0 <= i < 8 ==> \result[i] == a[i] * b[i] + c[i];
ensures \result == REG + \old(COUNTER) * 8;
ensures COUNTER == 1 + \old(COUNTER);
ensures \valid(\result + (0 .. 7));
ensures \valid_read(\result + (0 .. 7));
*/
__mm256 _mm256_fmadd_ps(__mm256 a, __mm256 b, __mm256 c);
