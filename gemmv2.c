#include "immintrin.h"
/*@
  axiomatic MatrixMult
  {
    inductive zeroed{L}(float* a, integer b, integer e){
    case zeroed_empty{L}:
        \forall float* a, integer b, e; b >= e ==> zeroed{L}(a, b, e);
    case zeroed_range{L}:
        \forall float* a, integer b, e; b < e ==>
        zeroed{L}(a, b, e-1) && a[e-1] == 0 ==> zeroed{L}(a,b,e);
  }
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

  lemma div8:
    \forall integer m; m % 16 == 0 ==> m % 8 == 0;
*/



/*@
  requires \valid_read(A + (0 .. M*K-1));
  requires \valid_read(B + (0 .. K*N-1));
  requires \valid(C + (0 .. M*N-1));
  requires COUNTER >= 1;
  requires \forall integer i; i>0 ==> \valid(REG + (0 .. i));
  requires \forall integer i; i>0 ==> \separated(REG + (0 .. i), A + (0 .. M*K-1), C + (0 .. M*N-1));
  requires \forall integer i; i>0 ==> \separated(REG + (0 .. i), B + (0 .. K*N-1), C + (0 .. M*N-1));
  requires M > 0 && N > 0 && K > 0;
  requires N % 16 == 0;
  ensures MatrixResult{Post}(A, B, C, M, K, N, M);
*/
void gemm_v2(int M, int N, int K, const float * A, const float * B, float * C)
{
    /*@
        loop invariant 0 <= i <= M;
        loop invariant MatrixResult{Here}(A, B, C, i, K, N, M);
        loop invariant COUNTER >= 1;
        loop invariant COUNTER >= \at(COUNTER, LoopEntry);
        loop assigns C[0 .. M*N-1], i, COUNTER;
        loop assigns REG[8*\at(COUNTER,LoopEntry) .. 8*COUNTER - 1];
        loop variant M-i;
    */
    for (int i = 0; i < M; ++i)
    {
        float * c = C + i * N;
        /*@ assert crow_bound: N + i*N <= M*N; */
        /*@ assert arow_bound: K + i*K <= M*K; */
        /*@
            loop invariant 0 <= j <= N;
            loop invariant j % 8 == 0;
            loop invariant 0 <= i < M;
            loop invariant zeroed{Here}(C, i*N, i*N + j);
            loop invariant COUNTER >= 1;
            loop invariant COUNTER >= \at(COUNTER, LoopEntry);
            loop invariant \separated(REG + (8*COUNTER .. 8*COUNTER+7), C + (0 .. M*N-1));

            loop assigns j, C[i*N .. i*N + N - 1], COUNTER;
            loop assigns REG[8*\at(COUNTER,LoopEntry) .. 8*COUNTER - 1];
            loop variant N-j;
        */
        for (int j = 0; j < N; j += 8)
        {
            /*@ assert zalign: j <= N - 8; */
            __mm256 z = _mm256_setzero_ps();
            /*@ assert z_sep_C: \separated(z + (0 .. 7), (c + j + 0) + (0 .. 7)); */
            _mm256_storeu_ps(c + j + 0, z);
            /*@ assert zeroed{Here}(C, i*N, i*N + j + 8);*/
        }
        /*@ assert zeroed{Here}(C, i*N, i*N + N);*/


        /*@
            loop invariant 0 <= k <= K;
            loop invariant 0 <= i < M;
			loop invariant \forall integer l; 0<=l<N ==> DotProduction(A, B, k, i, K, l, N, c[l]);
            loop invariant COUNTER >= 1;
            loop invariant COUNTER >= \at(COUNTER, LoopEntry);

            loop assigns k, C[i*N .. i*N + N - 1], COUNTER;
            loop assigns REG[8*\at(COUNTER,LoopEntry) .. 8*COUNTER - 1];
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
                loop invariant COUNTER >= 1;
                loop invariant COUNTER >= \at(COUNTER, LoopEntry);
                loop invariant \separated(REG + (8*COUNTER .. 8*COUNTER+7), B + (0 .. K*N-1));
                loop invariant \separated(REG + (8*COUNTER .. 8*COUNTER+7), C + (0 .. M*N-1));

                loop assigns C[i*N .. i*N + N - 1], j, COUNTER;
                loop assigns REG[8*\at(COUNTER,LoopEntry) .. 8*COUNTER - 1];
                loop variant N-j;
            */
            for (int j = 0; j < N; j += 16)
            {
               /*@ assert jalign: j <= N - 16; */
               /*@ assert step0: DotProduction(A, B, k+1, i, K, j, N, c[j]+a[0]*b[j]); */
               /*@ assert step1: DotProduction(A, B, k+1, i, K, j+1, N, c[j+1]+a[1]*b[j+1]); */
               /*@ assert step2: DotProduction(A, B, k+1, i, K, j+2, N, c[j+2]+a[2]*b[j+2]); */
               /*@ assert step3: DotProduction(A, B, k+1, i, K, j+3, N, c[j+3]+a[3]*b[j+3]); */
               /*@ assert step4: DotProduction(A, B, k+1, i, K, j+4, N, c[j+4]+a[4]*b[j+4]); */
               /*@ assert step5: DotProduction(A, B, k+1, i, K, j+5, N, c[j+5]+a[5]*b[j+5]); */
               /*@ assert step6: DotProduction(A, B, k+1, i, K, j+6, N, c[j+6]+a[6]*b[j+6]); */
               /*@ assert step7: DotProduction(A, B, k+1, i, K, j+7, N, c[j+7]+a[7]*b[j+7]); */
                __mm256 r0 = _mm256_fmadd_ps(a,
                    _mm256_loadu_ps(b + j + 0), _mm256_loadu_ps(c + j + 0));
                /*@ assert r0_sep_C: \separated(r0 + (0 .. 7), (c + j + 0) + (0 .. 7)); */
                _mm256_storeu_ps(c + j + 0, r0);
               /*@ assert step8: DotProduction(A, B, k+1, i, K, j+8, N, c[j+8]+a[0]*b[j+8]); */
               /*@ assert step9: DotProduction(A, B, k+1, i, K, j+9, N, c[j+9]+a[1]*b[j+9]); */
               /*@ assert step10: DotProduction(A, B, k+1, i, K, j+10, N, c[j+10]+a[2]*b[j+10]); */
               /*@ assert step11: DotProduction(A, B, k+1, i, K, j+11, N, c[j+11]+a[3]*b[j+11]); */
               /*@ assert step12: DotProduction(A, B, k+1, i, K, j+12, N, c[j+12]+a[4]*b[j+12]); */
               /*@ assert step13: DotProduction(A, B, k+1, i, K, j+13, N, c[j+13]+a[5]*b[j+13]); */
               /*@ assert step14: DotProduction(A, B, k+1, i, K, j+14, N, c[j+14]+a[6]*b[j+14]); */
               /*@ assert step15: DotProduction(A, B, k+1, i, K, j+15, N, c[j+15]+a[7]*b[j+15]); */
                __mm256 r1 = _mm256_fmadd_ps(a,
                    _mm256_loadu_ps(b + j + 8), _mm256_loadu_ps(c + j + 8));
                /*@ assert r1_sep_C: \separated(r1 + (0 .. 7), (c + j + 8) + (0 .. 7)); */
                _mm256_storeu_ps(c + j + 8, r1);
            }
            /*@ assert dot_done:  \forall integer l; 0<=l<N ==> DotProduction(A, B, k+1, i, K, l, N, c[l]);*/
        }
        /*@ assert row_done: RowResult{Here}(A, B, C, N, i, K, N); */
        /*@ assert mat_step: MatrixResult{Here}(A, B, C, i+1, K, N, M); */
    }
}
