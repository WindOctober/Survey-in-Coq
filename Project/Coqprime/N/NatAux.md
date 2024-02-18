# NatAux.v

在原始项目的src/CoqPrime/N/NatAux.v目录下

[github link](https://github.com/thery/coqprime/blob/master/src/Coqprime/N/NatAux.v)

这一部分中呈现了一些基本的`nat`类型的辅助引理的证明：

### minus_O
```
Theorem minus_O : 
    forall a b : nat, a <= b -> a - b = 0.
```
在自然数中，若$a<b$，则$a-b$的结果为0.

### pow

基本的求幂`pow`定义：
```
Fixpoint pow (n m: nat)  {struct m} : nat := 
    match m with 
    | O => 1%nat 
    | (S m1) => (n * pow n m1)%nat  
    end.
```
相关引理 `pow_add` `pow_pos` `pow_monotone` 分别描述了求幂时同底数的幂系数相加等价于两个同底数的幂相乘，幂的底数大于0则幂必然大于0，如果底数大于1，则幂的大小关于指数大小是单调的。（注意底数和幂都是自然数）

```
Theorem pow_add: 
    forall n m p, pow n (m + p) 
                = (pow n m * pow n p)%nat.

Theorem pow_pos: 
    forall p n, (0 < p)%nat 
                -> (0 < pow p n)%nat.

Theorem pow_monotone: 
    forall n p q, 
        (1 < n)%nat 
        -> (p < q)%nat 
        -> (pow n p < pow n q)%nat.
```

### divide
整除`divide`定义：
```
Definition divide a b := 
    exists c, b = a * c.
```

`divide_le`表示如果被除数大于1，除数整除被除数，那么除数一定小于被除数。【注：为了排除被除数为0的特殊情况，一切数整除0】
```
Theorem divide_le: 
    forall p q, 
        (1 < q)%nat 
        -> divide p q 
        -> (p <= q)%nat.
```
