#pragma once

/*
  v2: __mm256 моделируется как ЗНАЧЕНИЕ (struct из 8 float), а не как
  указатель в общую "растущую арену" REG. Реальный Си-код никогда не
  разыменовывает __mm256 через []  — это происходит только внутри ACSL
  (assert/ensures), поэтому смена представления не требует правок
  исполняемого кода gemmv2.c, только замены индексации `x[i]` на `x.e[i]`
  в логических формулах.

  Следствие: регистры больше не живут в общей памяти, поэтому между ними
  никогда не может быть алиасинга -- не нужны ни REG, ни COUNTER, ни
  \separated между регистрами. \valid/\separated остаются только там, где
  действительно идёт обращение к реальной памяти (loadu/storeu),
  как это и есть на практике.
*/

typedef struct { float e[8]; } __mm256;

/*@
  assigns \nothing;
  ensures \forall integer i; 0 <= i <= 7 ==> \result.e[i] == 0.0;
*/
__mm256 _mm256_setzero_ps(void);

/*@
  assigns \nothing;
  ensures \forall integer i; 0 <= i <= 7 ==> \result.e[i] == v;
*/
__mm256 _mm256_set1_ps(float v);

/*@
  requires \valid_read(a + (0 .. 7));
  assigns \nothing;
  ensures \forall integer i; 0 <= i <= 7 ==> \result.e[i] == a[i];
*/
__mm256 _mm256_loadu_ps(const float* a);

/*@
  requires \valid(mem_addr + (0 .. 7));
  assigns mem_addr[0 .. 7];
  ensures \forall integer i; 0 <= i <= 7 ==> mem_addr[i] == a.e[i];
*/
void _mm256_storeu_ps(float* mem_addr, __mm256 a);

/*@
  assigns \nothing;
  ensures \forall integer i; 0 <= i < 8 ==> \result.e[i] == a.e[i] * b.e[i] + c.e[i];
*/
__mm256 _mm256_fmadd_ps(__mm256 a, __mm256 b, __mm256 c);
