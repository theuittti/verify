#include "immintrin.h"
/*@
  axiomatic MatrixMult
  {

    predicate zeroed{L}(float* a, integer b, integer e) =
        \forall integer k; b <= k < e ==> a[k] == 0.0;
    inductive DotProduction(float* A, float* B, integer to,
                                   integer i, integer K, integer j, integer N, real res)
    {
    case dotproduction_empty_range:
      \forall float* A, float* B, integer to, integer i, integer K, integer j, integer N;
      0 >= to ==> DotProduction(A, B, to, i, K, j, N, 0.0);

    case dotproduction_positive_range:
      \forall float* A, float* B, integer to, integer i, integer K, integer j, integer N, real res;
      (0 < to) &&
      DotProduction(A, B, to-1, i, K, j, N, res) ==>
      DotProduction(A, B, to, i, K, j, N, res + A[i*K + (to-1)] * B[(to-1)*N + j]);

    }
    inductive RowResult{L2}(float* A, float* B, float* C, integer to,
                                integer i, integer K, integer N)
    {
      case rowresult_empty{L2}:
        \forall float* A, float* B, float* C, integer to, integer i, integer K, integer N;
        0 >= to ==> RowResult{L2}(A, B, C, to, i, K, N);

      case rowresult_step{L2}:
        \forall float* A, float* B, float* C, integer to, integer i, integer K, integer N;
        0 < to &&
        RowResult{L2}(A, B, C, to-1, i, K, N) &&
        DotProduction(A, B, K, i, K, (to-1), N, \at(C[i*N + (to-1)], L2))
        ==> RowResult{L2}(A, B, C, to, i, K, N);
    }

    inductive MatrixResult{L2}(float* A, float* B, float* C, integer to,
                                   integer K, integer N, integer M)
    {
      case matrixresult_empty{L2}:
        \forall float* A, float* B, float* C, integer to, integer K, integer N, integer M;
        0 >= to ==> MatrixResult{L2}(A, B, C, to, K, N, M);

      case matrixresult_step{L2}:
        \forall float* A, float* B, float* C, integer to, integer K, integer N, integer M;
        0 < to &&
        MatrixResult{L2}(A, B, C, to-1, K, N, M) &&
        RowResult{L2}(A, B, C, N, to-1, K, N)
        ==> MatrixResult{L2}(A, B, C, to, K, N, M);
    }
  }

  lemma math_bounds:
    \forall integer i, M, N;
    0 <= i < M && 0 < N ==> 0 <= i*N && i*N + N <= M*N;

  lemma mul_mono_nonneg:
    \forall integer x, y, z;
    x <= y && 0 <= z ==> x*z <= y*z;

  lemma div8:
    \forall integer m; m % 16 == 0 ==> m % 8 == 0;

  // Перенос фактов между двумя моментами времени (метками), когда
  // задействованные диапазоны A/B/C не менялись между ними.
  // Сами эти леммы прувер не докажет (внутри та же индукция, что и
  // в assert-ах) -- доказаны один раз в Coq, см. coq_prove/lemma_*.v
  lemma dp_frame{L1,L2}:
    \forall float* A, float* B, integer to, i, K, j, N, real res;
    (\forall integer idx; 0 <= idx < K*(i+1) ==> \at(A[idx],L1) == \at(A[idx],L2)) &&
    (\forall integer idx; 0 <= idx < N*K ==> \at(B[idx],L1) == \at(B[idx],L2)) &&
    0 <= i && 0 <= j < N && to <= K ==>
    \at(DotProduction(A,B,to,i,K,j,N,res),L1) ==> \at(DotProduction(A,B,to,i,K,j,N,res),L2);

  lemma row_frame{L1,L2}:
    \forall float* A, float* B, float* C, integer row, K, N, to;
    (\forall integer idx; 0 <= idx < K*(row+1) ==> \at(A[idx],L1) == \at(A[idx],L2)) &&
    (\forall integer idx; 0 <= idx < N*K ==> \at(B[idx],L1) == \at(B[idx],L2)) &&
    (\forall integer col; 0 <= col < N ==> \at(C[col+N*row],L1) == \at(C[col+N*row],L2)) &&
    0 <= row && 0 < N && to <= N ==>
    RowResult{L1}(A,B,C,to,row,K,N) ==> RowResult{L2}(A,B,C,to,row,K,N);

  lemma mat_frame{L1,L2}:
    \forall float* A, float* B, float* C, integer K, N, M, to;
    (\forall integer idx; 0 <= idx < K*to ==> \at(A[idx],L1) == \at(A[idx],L2)) &&
    (\forall integer idx; 0 <= idx < N*K ==> \at(B[idx],L1) == \at(B[idx],L2)) &&
    (\forall integer idx; 0 <= idx < N*to ==> \at(C[idx],L1) == \at(C[idx],L2)) &&
    0 < N && 0 < K && to <= M ==>
    MatrixResult{L1}(A,B,C,to,K,N,M) ==> MatrixResult{L2}(A,B,C,to,K,N,M);

  // Один блок из 8: "если 8 колонок были верны на шаге to-1, а C
  // обновили по формуле fmadd (av*B+C_old), то все 8 верны на шаге to".
  // Заменяет 8 отдельных assert-ов (step0..step7 / step8..step15) одним.
  lemma fmadd8_step{L1,L2}:
    \forall float* A, float* B, float* C, integer to, i, K, j, N, real av;
    0 < to && to <= K && 0 <= i && 0 <= j && j+8 <= N ==>
    (\forall integer idx; 0 <= idx < K*(i+1) ==> \at(A[idx],L1) == \at(A[idx],L2)) &&
    (\forall integer idx; 0 <= idx < N*K ==> \at(B[idx],L1) == \at(B[idx],L2)) &&
    av == \at(A[i*K+(to-1)], L1) &&
    (\forall integer q; 0 <= q < 8 ==> \at(DotProduction(A,B,to-1,i,K,j+q,N,C[j+q]),L1)) &&
    (\forall integer q; 0 <= q < 8 ==> \at(C[j+q],L2) == av*\at(B[(to-1)*N+(j+q)],L1) + \at(C[j+q],L1))
    ==> \forall integer q; 0 <= q < 8 ==> \at(DotProduction(A,B,to,i,K,j+q,N,C[j+q]),L2);
*/



/*@
  requires \valid_read(A + (0 .. M*K-1));
  requires \valid_read(B + (0 .. K*N-1));
  requires \valid(C + (0 .. M*N-1));
  requires \separated(A + (0 .. M*K-1), C + (0 .. M*N-1));
  requires \separated(B + (0 .. K*N-1), C + (0 .. M*N-1));
  requires M > 0 && N > 0 && K > 0;
  requires N % 16 == 0;
  ensures MatrixResult{Post}(A, B, C, M, K, N, M);
*/
void gemm_v2(int M, int N, int K, const float * A, const float * B, float * C)
{
    /*@
        loop invariant 0 <= i <= M;
        loop invariant MatrixResult{Here}(A, B, C, i, K, N, M);
        loop assigns C[0 .. M*N-1], i;
        loop variant M-i;
    */
    for (int i = 0; i < M; ++i)
    {
        float * c = C + i * N;
        /*@ assert crow_bound: N + i*N <= M*N; */
        /*@ assert arow_bound_aux: i+1 <= M; */
        /*@ assert arow_bound_mul: (i+1)*K <= M*K; */
        /*@ assert arow_bound: K + i*K <= M*K; */
        /*@
            loop invariant 0 <= j <= N;
            loop invariant j % 8 == 0;
            loop invariant 0 <= i < M;
            loop invariant zeroed{Here}(C, i*N, i*N + j);

            loop assigns j, C[i*N .. i*N + N - 1];
            loop variant N-j;
        */
        for (int j = 0; j < N; j += 8)
        {
            /*@ assert zalign: j <= N - 8; */
            __mm256 z = _mm256_setzero_ps();
            _mm256_storeu_ps(c + j + 0, z);
            /*@ assert zeroed{Here}(C, i*N, i*N + j + 8);*/
        }
        /*@ assert zeroed{Here}(C, i*N, i*N + N);*/


        /*@
            loop invariant 0 <= k <= K;
            loop invariant 0 <= i < M;
            loop invariant \forall integer l; 0<=l<N ==> DotProduction(A, B, k, i, K, l, N, c[l]);

            loop assigns k, C[i*N .. i*N + N - 1];
            loop variant K-k;
        */
        for (int k = 0; k < K; ++k)
        {
            const float * b = B + k * N;
            /*@ assert brow_bound: N + k*N <= K*N; */
            __mm256 a = _mm256_set1_ps(A[i*K + k]);
            /*@
                loop invariant 0 <= j <= N;
                loop invariant 0 <= k < K;
                loop invariant 0 <= i < M;
                loop invariant j % 16 == 0;
                loop invariant \forall integer q; 0 <= q < j ==> DotProduction(A, B, k+1, i, K, q, N, c[q]);
                loop invariant \forall integer q; j <= q < N ==> DotProduction(A, B, k, i, K, q, N, c[q]);

                loop assigns C[i*N .. i*N + N - 1], j;
                loop variant N-j;
            */
            for (int j = 0; j < N; j += 16)
            {
               /*@ assert jalign: j <= N - 16; */
               /*@ assert valid_b_bound: k*N + j + 16 <= K*N; */
               /*@ assert b_eq: \forall integer q; j <= q < j+16 ==> b[q] == B[k*N + q]; */
               /*@ assert valid_b: \valid_read(b + j + (0 .. 15)); */
               /*@ assert valid_c: \valid(c + j + (0 .. 15)); */
               /*@ assert a_eq: a.e[0] == A[i*K + k]; */
                J16Top: ;
                __mm256 r0 = _mm256_fmadd_ps(a,
                    _mm256_loadu_ps(b + j + 0), _mm256_loadu_ps(c + j + 0));
                _mm256_storeu_ps(c + j + 0, r0);
               /*@ assert block0: \forall integer q; 0<=q<8 ==> DotProduction(A, B, k+1, i, K, j+q, N, c[j+q]); */
                __mm256 r1 = _mm256_fmadd_ps(a,
                    _mm256_loadu_ps(b + j + 8), _mm256_loadu_ps(c + j + 8));
                _mm256_storeu_ps(c + j + 8, r1);
               /*@ assert block1: \forall integer q; 0<=q<8 ==> DotProduction(A, B, k+1, i, K, j+8+q, N, c[j+8+q]); */
            }
            /*@ assert dot_done:  \forall integer l; 0<=l<N ==> DotProduction(A, B, k+1, i, K, l, N, c[l]);*/
        }
        /*@ assert row_done: RowResult{Here}(A, B, C, N, i, K, N); */
        /*@ assert mat_step: MatrixResult{Here}(A, B, C, i+1, K, N, M); */
    }
}
