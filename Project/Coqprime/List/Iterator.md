# Iterator.v

在原始项目的src/Coqprime/List/Iterator.v目录下。

[github link](https://github.com/thery/coqprime/blob/master/src/Coqprime/List/Iterator.v)

主要定义了一些关于列表的操作，以及与之定义的相关性质。

### Section: Iterator

引入了一个Section，两个集合`A,B`，以及这两个集合中的基本性质。

规定了 `B` 集合中的零元 `zero` ，两个函数 `f : A -> B` ， `g : B -> B -> B` ，以及关于这两个函数的性质：

1. `g_zero`: 函数`g`在读入任意元素`a`和零元时，返回`a`。
   ```
   Hypothesis g_zero : forall a,  g a zero = a.
   ```
2. `g_trans`: 函数`g`，类似左结合的性质。
   ```
   Hypothesis g_trans : forall a b c,  
        g a (g b c) = g (g a b) c.
   ```
3. `g_sym`: 函数`g`，参数交换结果一致。
   ```
   Hypothesis g_sym : forall a b,  g a b = g b a.
   ```

在定义完函数的基本性质之后，引入了列表和处理列表用的一系列函数及对应的性质。

`iter`: 读入一列集合`A`中的元素，将其通过`f`转化为B集合中的元素后，依次与g作用，得到类型为`B`的一个结果。
```
Definition iter := fold_right (fun a r => g (f a) r) zero.
```

对应的性质为：

1. `iter_app`: 对`l1`和`l2`连接之后的列表做迭代(`iter`)，和分别迭代之后的结果再用函数`g`作用的结果是一致的。
   ```
   Theorem iter_app: forall l1 l2,  
        iter (app l1 l2) = g (iter l1) (iter l2).
   ```
2. `iter_permutation`: 如果`l1`为`l2`的置换（permutation），则两个列表迭代结果一致。
   ```
    Theorem iter_permutation: forall l1 l2, 
        permutation l1 l2 ->  iter l1 = iter l2.
   ```
3. `iter_inv`: 证明与`iter`相关性质时的归纳法，首先对零元`zero`归纳，证明`P zero`。其次对函数`g`作用的结果归纳，要求`P a -> P b -> P (g a b)`。最后对列表中的元素归纳，要求所有在列表中的元素`x`，都满足`P (f x)`。综上则有 `P (iter l)`。【类似type_ind】

    ```
    Lemma iter_inv: forall P l,
    P zero ->
    (forall a b, P a -> P b ->  P (g a b)) ->
    (forall x, In x l -> P (f x)) ->  
    P (iter l).
    ```

为了更好的表示和创建列表，这里额外引入了`next: A -> A`，来表示类型为`A`的列表中当前元素的下一个，并结合`progression`构造了一个列表。

```
Fixpoint progression (m : A) (n : nat) {struct n} : list A :=
    match n with   
    | 0 => nil
    | S n1 => cons m (progression (next m) n1) 
    end.
```

而为了表示相对当前位置索引为`i`的元素，引入了`next_n`的定义：

```
Fixpoint next_n (c : A) (n : nat) {struct n} : A :=
    match n with 
    | 0 => c 
    | S n1 => next_n (next c) n1 
    end.
```

综上，得到一些泛用的结论：

1. `progression_app`: `progression a n`创建了以当前元素`a`为首，长度为`n`的列表，而列表中的具体元素由`next`函数决定。`progression_app`表示如果从列表中间第`m`个元素的位置断开，分别将`progression a m`和`progression b (n - m)`两个索引分别为`[0,m-1]`，`[m,n-1]`的列表连接在一起的结果和之前的列表是一致的。
    ```
    Theorem progression_app: forall a b n m,
        le m n -> b = next_n a m ->
        progression a n = app (progression a m) (progression b (n - m)).
    ```

2. `iter_progression_app`: 类似上述引理，这里决定了连接前后的列表在`iter`下的结果依旧是一致的。

    ```
    Theorem iter_progression_app: forall a b n m,
        le m n -> b = next_n a m ->
        iter (progression a n)
        = g (iter (progression a m)) (iter (progression b (n - m))).
    ```

3. `length_progression`: `progression x n`生成的列表长度为`n`。
   ```
   Theorem length_progression: forall z n,  
        length (progression z n) = n.
   ```

### Extra Lemma for iter & progression (out of section)

`iter_ext`: 对于`f: A -> B`，如果存在两个函数`f1`，`f2`，满足`forall a, f1 a = f2 a`，那么他们对于相同零元`zero`和相同迭代列表`l`与迭代函数`g`下的迭代结果一致。

```
Theorem iter_ext: forall (A B : Set) zero (f1 : A ->  B) f2 g l,
    (forall a, In a l -> f1 a = f2 a) ->  
    iter zero f1 g l = iter zero f2 g l.
```

`iter_map`: 如果对于`k: A -> B`，`f: B -> C`两个函数，将`k`，`f`先后作用于被迭代的列表`l`上的结果和提前对列表`l`使用`map`函数作用为`map k l`再用`iter f`的结果是一致的。

```
Theorem iter_map: forall (A B C : Set) zero (f : B ->  C) g (k : A ->  B) l,
  iter zero f g (map k l) = iter zero (fun x => f (k x)) g l.
```

`iter_comp`: 将列表`l`在`f1`，`f2`迭代的结果由`g`作用后的值和将变换函数`f`修改为`fun x => g (f1 x) (f2 x)`来变换`l`再由`g`迭代之后的结果是一致的。 
```
Theorem iter_comp: forall (A B : Set) zero (f1 f2 : A ->  B) g l,
    (forall a,  g a zero = a) ->
    (forall a b c,  g a (g b c) = g (g a b) c) ->
    (forall a b,  g a b = g b a) ->
    g (iter zero f1 g l) (iter zero f2 g l) 
    = iter zero (fun x => g (f1 x) (f2 x)) g l.
```

`iter_com`: `TODO` 应是与后续结合使用的引理，本身是一种特定变换函数下的交换律。
```
Theorem iter_com: forall (A B : Set) zero (f : A -> A ->  B) g l1 l2,
    (forall a,  g a zero = a) ->
    (forall a b c,  g a (g b c) = g (g a b) c) ->
    (forall a b,  g a b = g b a) ->
    iter zero (fun x => iter zero (fun y => f x y) g l1) g l2
    = iter zero (fun y => iter zero (fun x => f x y) g l2) g l1.
```

`iter_comp_const`: 如果存在一个函数`k: B -> B`，那么基于`f`，`g`的`iter`函数在对`l`迭代之后的结果被`k`作用的结果和将变换函数`f`改为`k f`再对`l`迭代的结果是一致的。

```
Theorem iter_comp_const: forall (A B : Set) zero (f : A ->  B) g k l,
    k zero = zero ->
    (forall a b,  k (g a b) = g (k a) (k b)) ->
    k (iter zero f g l) = iter zero (fun x => k (f x)) g l.
```

`next_n_S`: 若`next`函数为`S`，那么`next_n S n m`本质上就是自然数加法。

```
Lemma next_n_S: forall n m,  next_n S n m = plus n m.
```

`progression_S_le_init`,`progression_S_le_end`: 以`S`作为`next`函数，得到的序列范围约束。

```
Theorem progression_S_le_init: forall n m p, 
    In p (progression S n m) -> le n p.

Theorem progression_S_le_end: forall n m p, 
    In p (progression S n m) -> lt p (n + m).
```