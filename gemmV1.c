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
*/


/*@
  requires \valid_read(A + (0 .. M*K-1));
  requires \valid_read(B + (0 .. K*N-1));
  requires \valid(C + (0 .. M*N-1));
  requires \separated(A + (0 .. M*K-1), C + (0 .. M*N-1));
  requires \separated(B + (0 .. N*K-1), C + (0 .. M*N-1));
  requires M > 0 && N > 0 && K > 0;
  
  ensures MatrixResult{Post}(A, B, C, M, K, N, M);
*/


void gemm_v1(int M, int N, int K, const float * A, const float * B, float * C)
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

        /*@
            loop invariant 0 <= j <= N;
            loop invariant 0 <= i < M;
            loop invariant zeroed{Here}(C, i*N, i*N + j);
            
            loop assigns j, C[i*N .. i*N + N - 1]; 
            loop variant N-j;
        */
        for (int j = 0; j < N; ++j)
        {
            c[j] = 0;
            /*@ assert zeroed{Here}(C, i*N, i*N + j + 1);*/  
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
            float a = A[i*K + k];
            /*@
                loop invariant 0 <= t <= N;
                loop invariant 0 <= k < K;
                loop invariant 0 <= i < M;
                loop invariant \forall integer q; 0<=q<t ==> DotProduction(A, B, k+1, i, K, q, N, c[q]);
                loop invariant \forall integer q; t <= q < N ==> DotProduction(A, B, k, i, K, q, N, c[q]);
                loop assigns t, C[i*N .. i*N + N - 1];
                loop variant N-t;
            */
            for (int t = 0; t < N; ++t)
            {
                /*@ assert step: DotProduction(A, B, k+1, i, K, t, N, c[t]+a*b[t]); */
                c[t] += a * b[t];
            }
            /*@ assert dot_done:  \forall integer l; 0<=l<N ==> DotProduction(A, B, k+1, i, K, l, N, c[l]);*/
        }
        /*@ assert row_done: RowResult{Here}(A, B, C, N, i, K, N); */
        /*@ assert mat_step: MatrixResult{Here}(A, B, C, i+1, K, N, M); */
    }
}

//че ваще есть: матрицы A B C 
//				размеры M N K
//              перемен a   пересечение i-той строки и k-того столбца матрицы A
//				индексы i j k t
//				указтль * c на начало i-той строки матрицы C
//				указтль * b на начало k-той строку матрицы B

//A B ВАЩЕ НИКАК НЕ МЕНЯЮТСЯ ПО ХОДУ ВЫПОЛНЕНИЯ ПРОГРАММЫ
//M N K НИКАК НЕ МЕНЯЮТСЯ ПО ХОДУ ПРОГРАММЫ
//C МЕНЯЕТСЯ ПО ОПИСАННОЙ АКСИОМАТИКЕ
//i от 0 до M-1
//j от 0 до N-1
//k от 0 до K-1
//sum = произведению строки на столбец
