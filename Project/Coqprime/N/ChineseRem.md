# ChineseRem.v

在原始项目的src/Coqprime/N/ChineseRem.v目录下。

[github link](https://github.com/thery/coqprime/blob/master/src/Coqprime/N/ChineseRem.v)

这部分围绕中国剩余定理，展开了一系列关于互素、整除、除法运算相关的性质证明。

### Compatibility Lemmas
为了避免版本带来的兼容性问题，这一文件中证明了一些8.16之前标准库并不具有的基础引理，方便后续证明时使用。

1. *`mult_O_le`*: 对一个自然数乘一个非零数，结果必然大于原来的自然数
    ```
    Lemma mult_O_le : 
        forall n m : nat, 
            m = 0%nat 
            \/ (n <= m * n)%nat.
    ```

2. *`le_plus_trans`*: 在`le`右侧加上一个自然数保持大小关系。
    ```
    Lemma le_plus_trans (n m p : nat) : 
        (n <= m)%nat -> (n <= m + p)%nat.
    ```
3. *`ltgt1`*: 如果一个自然数严格大于另一个自然数，那么这个自然数一定大于0
   ```
   Lemma ltgt1: forall a b : nat, (a < b -> b > 0)%nat. 
   ```
4. *`minus1`*: 如果两个整数分别减去了一个相同的整数之后结果相同，那么这两个整数相同。
   ```
   Lemma minus1: forall a b c : Z, 
        (a - c)%Z = (b - c)%Z -> a = b.
   ```
5. *`minusS`*: 两个自然数相减，和两个自然数的后继相减的结果一致
   ```
   Lemma minusS : forall a b : nat, b - a = S b - S a.
   ```
6. *`div_trans`*: `divide`具有传递性。
   ```
   Lemma div_trans (p q r: nat) : 
        divide p q -> divide q r -> divide p r.
   ```
7. *`div_refl`*: `divide`具有自反性
   ```
   Lemma div_refl p : divide p p.
   ```
8. *`prod`*: nat -> (nat -> nat) -> nat，读入一个自然数`n`，函数`f: nat -> nat`，返回$f(n-1)*f(n-2)\ldots *f(1)*f(0)$，其中$f(0)=1$.
   ```
    Fixpoint prod (n:nat) (x: nat -> nat) :=
        match n with
        | O => 1%nat
        | S p => x p * prod p x
        end.
    ```
9.  *`prodBig1`*: 如果上述的函数对于所有$x<n,f(x)>0$，那么最终`prod n f`的结果大于零。
    ```
    Lemma prodBig1 : forall (n : nat) (x : nat -> nat),
            (forall z : nat, z < n -> x z > 0) 
            -> prod n x > 0.
    ```
10. *`prodExtensional`*: 如果对于所有$x<n,f_1(x)=f_2(x)$，那么最终`prod n f1=prod n f2`
    ```
    Lemma prodExtensional : 
        forall (n : nat) (x1 x2 : nat -> nat),
        (forall z : nat, z < n -> x1 z = x2 z) 
        -> prod n x1 = prod n x2.
    ```

除了以上的一些引理之外，还引申了阶乘的定义：
```
Definition factorial (n : nat) : nat := prod n S.
```

### CoPrime

关于两个自然数互素的定义，引用了`ZArith`标准库中的`Zis_gcd`来定义，这是一个`Z->Z->Z->Prop`的函数，`Zis_gcd a b d`表示$gcd(a,b)=d$，即如下定义：

```
Definition CoPrime (a b : nat) := 
    Zis_gcd (Z.of_nat a) (Z.of_nat b) 1%Z.
```

首先是这一定义的对称性，即 *`coPrimeSym`*:

```
Lemma coPrimeSym: forall a b : nat, CoPrime a b -> CoPrime b a.
```

**Bezout**

其次是关于Bezout等式([wiki link](https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity))在coq中的定义，在`ZArith.Znumtheory`库下.
```
Inductive Bezout (a b d : Z) : Prop :=
	Bezout_intro : forall u v : Z, 
        (u * a + v * b)%Z = d -> Bezout a b d.
```

> Bezout引理为：设 $a$ 和 $b$ 为整数，它们的最大公约数为 $d$。那么存在整数 $x$ 和 $y$，使得 $ax + by = d$。此外，形如 $az + bt$ 的整数恰好是 $d$ 的倍数。

而在项目中也有对应定理（自然数版本）：【注：之所以需要这一引理，是为了方便后续证明中，将最大公约数的定义转化为构造性的，存在某一对整数$x,y使得等式成立。】

```
Lemma gcd_bezout_nat: forall (x y d : nat),
  (x > 0)%nat ->
  Zis_gcd (Z_of_nat x) (Z_of_nat y) (Z_of_nat d) ->
  Bezout (Z_of_nat x) (Z_of_nat y)  (Z_of_nat d).
```

*`coPrimeMult`*: 数论中的经典结论，如果$a,b$互素，且$a$整除$b*c$，那么$a$整除$c$.

```
Lemma coPrimeMult : forall a b c : nat, 
    CoPrime a b -> divide a (b * c) -> divide a c.
```

*`coPrimeMult2`*: 如果$a,b$互素，且$a,b$分别整除$c$，那么$a*b$整除c。

```
Lemma coPrimeMult2 : forall a b c : nat,
    CoPrime a b -> divide a c -> divide b c 
    -> divide (a * b) c.
```

### Euclid + Chinese Remainder Theorem

*`chRem2`*: 如果$r1,r2$都属于$[0,q)$的范围内，则任意一个能表示为$a*q+r$形式的数，其$r$是惟一的（实际上$a$也是惟一的）。

```
Lemma chRem2 : 
  forall b1 r1 b2 r2 q : Z,
    (0 <= r1)%Z -> (0 <= r2)%Z ->
    (r1 < q)%Z -> (r2 < q)%Z -> 
    (b1 * q + r1)%Z = (b2 * q + r2)%Z ->
    r1 = r2.
```

*`uniqueRem`*: 可以说是`chRem2`的另一种表达，但这里限定了自然数类型，并且说明了$a/b$除法运算中，商和余数的惟一性。【要求除数大于零】

```
Lemma uniqueRem :
    forall r1 r2 a b : nat,
        b > 0 -> 
        (exists q : nat, a = q * b + r1 /\ b > r1) ->
        (exists q : nat, a = q * b + r2 /\ b > r2) -> 
        r1 = r2.
```

*`div_eucl`*: 上述定理的另一种表达，即在除数大于零的情况下，对于任意的被除数和除数，均存在一组对应的商和余数。

```
Lemma div_eucl :
    forall b : nat,  b > 0 ->
    forall a : nat, 
        {p : nat * nat | a = fst p * b + snd p 
                            /\ b > snd p}.
```

*`chRem1`*: 这是div_eucl的商为负数的情况，此时`fst p`的类型改为Z。

```
Lemma chRem1 : 
 forall b : nat,  b > 0 -> forall a : Z,
     {p : Z * nat | snd p < b 
                    /\ Z.of_nat (snd p) 
                        = (fst p * Z.of_nat b + a)%Z}.
```

*`euclid_gcd1`*: 即 $gcd(q*y+r,y)=gcd(r,y)$的数论推理。

```
Lemma euclid_gcd1 :
  forall (d : nat) (x y q r : Z),
    Zis_gcd x y (Z.of_nat d) -> 
    x = (q * y + r)%Z ->
    Zis_gcd r y (Z.of_nat d).
```

*`euclid_gcd`*: 同上

```
Lemma euclid_gcd (d1 d2 : nat) (x y q r : Z) :
   x = (q * y + r)%Z -> 
   Zis_gcd x y (Z.of_nat d1) ->
   Zis_gcd r y (Z.of_nat d2) -> 
   d1 = d2.
```

*`gcd_lincomb_nat_dec`*: 即两个数$a,b$的最大公约数$d$可以表示为$\exists u\ v,s.t.\ u*a+v*b=d$.

```
Lemma gcd_lincomb_nat_dec : forall x y d : nat,
 x > 0 ->
 Zis_gcd (Z.of_nat x) (Z.of_nat y) (Z.of_nat d) ->
 {a : Z * Z |
   Z.of_nat d 
   = (Z.of_nat x * fst a + Z.of_nat y * snd a)%Z}.
```

`chineseRemainderTheoremHelp`: 中国剩余定理的一个方向。中国剩余定理（仅限两数之间）的定义为：给定一组两两互质的自然数`x1`和`x2`以及它们对应的余数`a`和`b`时，存在一个自然数`y`，使得`y`除以`x1`的余数是`a`，且`y`除以`x2`的余数是`b`.

而为了方便证明，这里对余数`a`,`b`的大小进行了区分，辅助引理讨论的是`a<=b`的方向。

```
Lemma chineseRemainderTheoremHelp :
  forall x1 x2 : nat,
    CoPrime x1 x2 ->
    forall (a b : nat) (pa : a < x1) (pb : b < x2),
      a <= b ->
      {y : nat |
        y < x1 * x2 /\
        a = snd (proj1_sig (div_eucl x1 (ltgt1 _ _ pa) y)) /\
        b = snd (proj1_sig (div_eucl x2 (ltgt1 _ _ pb) y))}.
```

`chineseRemainderTheorem`: 中国剩余定理，去掉上述辅助引理中的`a<=b`项。

`coPrime1` : Coprime的基本性质，1和所有自然数互素。

```
Lemma coPrime1 : forall a : nat, CoPrime 1 a.
```

`coPrimeMult3`: Coprime在非零自然数乘法中的结论——$a,b$分别与$c$互素，则$a*b$与$c$互素。

```
Lemma coPrimeMult3 (a b c: nat):
  a > 0 -> b > 0 -> c > 0 ->
  CoPrime a c -> CoPrime b c -> CoPrime (a * b) c.
```

`coPrimeProd`: 基于先前定义的`prod`的基础上定义的一个互素性质。对于所有小于等于自然数$n$的不等自然数对$x,y$ ($x\ne y$)，$f(x)$与$f(y)$互素，且$f(x)\ne 0$，那么`prod n f` 和 $f(n)$互素。注意这里的`prod n f` = $f(n-1)*f(n-2)\ldots *f(1)*f(0)$。

```
Lemma coPrimeProd : forall (n : nat) (x : nat -> nat),
    (forall z1 z2 : nat, 
        z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)) ->
    (forall z : nat, z < S n -> x z > 0) -> 
    CoPrime (prod n x) (x n).
```

`divProd`: 这说的是$f(i)$整除`prod n f`，当$i<n$时。

```
Lemma divProd : forall (n : nat) (x : nat -> nat) (i : nat),
    i < n -> divide (x i) (prod n x).
```

`chRem`: 完整版的中国剩余定理（之前是仅限两个数下的结果），其中核心是通过`x: nat -> nat`这样一个函数表达了一个n元数组。而中国剩余定理（自然数版本）的定义如下：对任意n个两两互素的自然数$\{a_i\}$，与n个任意自然数 $\{b_i\}$满足 $\forall i, a_i>b_i$，存在一个自然数$x$，满足$x\equiv b_i\mod a_i$。

```
Lemma chRem : forall (n : nat) (x : nat -> nat),
    (forall z1 z2 : nat, 
        z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)) ->
    forall (y : nat -> nat) (py : forall z : nat, z < n -> y z < x z),
    {a : nat |
    a < prod n x /\
    (forall (z : nat) (pz : z < n),
    y z = snd (proj1_sig (div_eucl (x z) (ltgt1 _ _ (py z pz)) a)))}. 
```

### prime

重载`Prime`的定义【Z中有prime的定义】

```
Definition Prime (n : nat) : Prop :=
  n > 1 /\ (forall q : nat, divide q n -> q = 1 \/ q = n).
```

`divdec`: `divide`的可判定性。

```
Lemma divdec : forall n d : nat, 
    divide d n \/ ~ divide d n.
```

`prime_Prime`: 重载的定义和标准库中的`prime`定义之间的蕴含关系。[prime -> Prime]

```
Lemma prime_Prime (n: nat) : prime (Z.of_nat n) -> Prime n.
```

`Prime_prime`: Prime -> prime

```
Lemma Prime_prime (n: nat) : Prime n -> prime (Z.of_nat n).
```

`Prime_dec`: Prime的可判定性

```
Lemma Prime_dec (n: nat) : Prime n \/ ~ Prime n.
```

`primeDiv`: 对于任意一个大于1的正整数，他一定可以被一个素数整除。

```
Lemma primeDiv : forall a : nat, 
    1 < a ->
    exists p : nat, Prime p /\ divide p a.
```

`coPrimePrime`: 对于自然数$a,b$，如果任意的素数不同时整除$a$和$b$，则$a,b$互素。

```
Lemma coPrimePrime : forall a b : nat,
   (forall p : nat, Prime p -> 
        ~ divide p a \/ ~ divide p b) ->
   CoPrime a b.
```

`div_plus_r`: 如果两个数$a,b$相加的和被一个自然数$d$整除，且$a$被$d$整除，那么$b$一定被$d$整除。

```
Lemma div_plus_r : forall a b d : nat, 
    divide d a -> divide d (a + b) -> divide d b.
```

`div_mult_compat_l`: $a \mid b$ 蕴含 $a\mid b*c$。

```
Lemma div_mult_compat_l : forall a b c : nat, 
    divide a b -> divide a (b * c).
```

`primedivmult`: $p$为素数，$p\mid a*b$，则要么$p\mid a$，要么$p\mid b$。

```
Lemma primedivmult : forall p n m : nat,
  Prime p -> divide p (n * m) -> 
  divide p n \/ divide p m.
```

`coPrimeSeqHelp`: 假设$\forall c$,满足 $n!\mid c$，并且对于任意的$i<j,i<=n,j<=n$的一对自然数对$(i,j)$，我们有$c*(i+1)+1$ 和 $c*(j+1)+1$ 互素。

```
Lemma coPrimeSeqHelp : forall c i j n : nat,
 divide (factorial n) c ->
 i < j -> i <= n -> j <= n -> 
 CoPrime (S (c * S i)) (S (c * S j)).
```

### Goedel's beta function

关于余数`rem`的表达: 这里的`div_eucl`即存在一个自然数对，分别表示$a\div b$的商和余数，而`proj1_sig`取出了这个存在的值对的具体值，然后`snd`表示值对的第二个元素，即余数。

```
#[global] Notation rem a b Hposb :=
  (snd (proj1_sig (div_eucl b Hposb a))).
```

`coPrimeBeta`: 形如$x*(i+1)+1$形式的数，随着i的增加，能构成一组互素的序列。

```
Definition coPrimeBeta (z c : nat) : nat := S (c * S z).
```

`gtBeta`: Beta数大于零。
```
Lemma gtBeta : forall z c : nat, 
    coPrimeBeta z c > 0.
```

`beta`: x mod (y*(z+1)+1)的结果。

```
Definition beta x y z := rem x (S (z * S y)) (gtBeta _ _).
```

`coPrimeSeq`: coPrimeBeta数列(`coPrimeBeta i c`,满足$0<=i<=n$)，在$n!\mid c$时，生成的序列两两互素。

```
Lemma coPrimeSeq : forall c i j n : nat,
    divide (factorial n) c ->
    i <> j -> i <= n -> j <= n ->
    CoPrime (coPrimeBeta i c) (coPrimeBeta j c).
```

`maxBeta`: 求生成序列中的最大数。

```
Fixpoint maxBeta (n: nat) (x: nat -> nat) :=
  match n with
  | 0 => 0
  | S n => Nat.max (x n) (maxBeta n x)
  end.
```

`maxBetaLe`: 证明`maxBeta`得到的确实是有限序列中的最大数。

```
Lemma maxBetaLe : forall (n : nat) (x : nat -> nat) (i : nat),
    i < n -> x i <= maxBeta n x.
```

`divProd2`: 子序列累乘`prod i f` ( $i<=n$) 的结果整除完整序列累乘`prod n f`的结果。

```
Theorem divProd2 : forall (n : nat) (x : nat -> nat) (i : nat),
    i <= n -> divide (prod i x) (prod n x).
```

`betaTheorem1`: 中国剩余定理的应用，此处两两互素的元素即`coPrimeBeta`构成的序列，而余数序列则由`y i`来表示。

```
Theorem betaTheorem1 : forall (n : nat) (y : nat -> nat),
 {a : nat * nat | forall z : nat,
    z < n ->
    y z = snd (proj1_sig (div_eucl (coPrimeBeta z (snd a))
                        (gtBeta z (snd a)) (fst a)))}.
```

`betaTheorem`: 用`beta`记号来整理上述定理。`beta x y z`即`rem x (coPrimeBeta y z)`，而`(coPrimeBeta y z)`即由$[0,n-1]$中的索引$z$构成的Beta序列。

```
Lemma betaTheorem :
  forall (n : nat) (y : nat -> nat),
    {a : nat * nat
    | forall z : nat, z < n -> y z = beta (fst a) (snd a) z}.
```
