# AVX-vectorized GEMM — деductive verification (Frama-C/WP + Coq), v2

Верификация умножения матриц `C = A * B` через AVX-интринсики, v2 отличается
от [`main_work`](../main_work) **моделью регистра `__m256`**: вместо указателя
в общую "растущую арену" (`REG` + `COUNTER`) регистр теперь моделируется как
**значение** (struct из 8 float), как он и есть физически.

## Идея изменения

В v1 каждый вызов интринсика, возвращающего регистр, "выделял" новый слот в
глобальном массиве `REG` и должен был доказывать неперекрытие этого слота со
всеми остальными регистрами и с A/B/C. Это порождало значительную часть
инвариантов циклов (`COUNTER >= ...`, поточечный `\separated(REG+(...), ...)`)
и обслуживающих их целей.

В v2 (`immintrin.h`):

```c
typedef struct { float e[8]; } __mm256;
```

Регистр больше не живёт в общей памяти — он копируется по значению, как
`int`. Между двумя `__mm256`-значениями по определению не может быть
алиасинга, поэтому `REG`/`COUNTER` и все связанные с ними `requires`/
`loop invariant`/`assert` (`z_sep_C`, `r0_sep_C`, `r1_sep_C` и т.п.) просто
исчезают. `\valid`/`\valid_read`/`\separated` остаются только там, где
действительно идёт обращение к реальной памяти — в `_mm256_loadu_ps` и
`_mm256_storeu_ps`.

Реальный Си-код (`gemmv2.c`) не менялся вообще — `__mm256`-значения там
никогда не разыменовывались через `[]`. Правки только в ACSL: `a[0]` →
`a.e[0]` внутри `assert`-подсказок (`step0`..`step15`, `a_eq`), плюс убраны
все строки про `REG`/`COUNTER`.

## Результат прогона (то же окружение: Frama-C 33.0 Arsenic + Alt-Ergo)

| | baseline (`main_work`) | v2 (`main_work_v2`) |
|---|---|---|
| Целей всего | 184 | **113** (−39%) |
| Proved | 85 | 51 |
| Qed | 84 | 50 |
| Alt-Ergo | 1 | 1 |
| Failed | 98 | **61** (−38%) |
| Timeout | 1 | 1 |

Доля доказанного (≈46%) осталась примерно той же, но **абсолютное число
целей, которые остаётся добивать вручную в Coq, упало почти на 40%** —
именно за счёт того, что вся "бухгалтерия" регистровой арены исчезла целиком
и её больше не нужно ни специфицировать, ни доказывать.

Сверка списков непройденных целей подтверждает: единственное, что
исчезло — это в точности REG/COUNTER-специфичные цели
(`assert_z_sep_C`, `assert_r0_sep_C`, `assert_r1_sep_C`, `requires` для
`_mm256_setzero_ps`/`_mm256_set1_ps`/`_mm256_fmadd_ps`). Оставшиеся непройденные
цели (`crow_bound`/`arow_bound`/`brow_bound`, `step0..step15`,
`dot_done`/`row_done`/`mat_step`, `rte_signed_overflow`) — те же самые, что и
в v1: это "настоящая" математика задачи (нелинейная арифметика индексов и
шаги `DotProduction`), которая и так требовала ручного доказательства в Coq
и не связана с моделью регистра.

## Как прогнать

```bash
frama-c -wp -wp-rte -wp-timeout 10 gemmv2.c
```

## Источники

Перед выбором struct-значения как модели регистра были проверены и другие
варианты:

- [ACSL malloc-контракт (`\fresh`/`allocates`)](https://github.com/acsl-language/acsl/blob/master/malloc-free2-fn.c) —
  стандартный ACSL-паттерн для функции, возвращающей заведомо свежий,
  ни с чем не пересекающийся блок памяти (`ensures \fresh(\result, n)`).
  Выглядит как готовое решение для "регистр = свежевыделенный блок", но:
- [Frama-C-discuss: регионы WP для malloc-аксиоматики](https://frama-c.com/html/fc-discuss/2017-March/msg00003.html) —
  выяснилось, что WP не поддерживает `\fresh`/`allocates` нативно и не
  выводит из них разделение памяти автоматически; нужна ручная аксиоматика
  через внутренние "регионы" WP — по объёму работы это то же самое, что и
  наш `REG`/`COUNTER`, просто другими словами. Это же подтверждает и
  `notes/frama-c-wp-manual.pdf` (раздел 1.6 Limitations & Roadmap:
  *"Dynamic allocation... ACSL clauses for specifying allocation and
  deallocation are not implemented yet"*). Путь признан тупиковым для
  используемой версии WP.
- [HACLxN: Verified Generic SIMD Crypto](https://project-everest.github.io/assets/haclxn.pdf) и
  [EverCrypt: A Fast, Verified, Cross-Platform Cryptographic Provider](https://www.researchgate.net/publication/343340372_EverCrypt_A_Fast_Verified_Cross-Platform_Cryptographic_Provider) —
  прецедент из индустрии формальной верификации: в верифицированном
  SIMD-крипто-коде (Vale/Jasmin, используемые в HACL*/EverCrypt) регистр
  моделируется как **значение** в состоянии абстрактной машины, а не как
  адрес в куче. Это и есть содержательное обоснование выбора struct-подхода
  в v2 — не просто технический трюк, а устоявшийся паттерн моделирования
  SIMD-регистров в деductive verification.
