# ListAux.v

在原始项目的src/Coqprime/List/ListAux.v目录下。

[github link](https://github.com/thery/coqprime/blob/master/src/Coqprime/List/ListAux.v)


### list in Coq

`list_length_ind`: 对列表长度进行的归纳法定义，归纳的目标是一个命题（某一种性质）。
```
Theorem list_length_ind: forall (P : list A -> Prop),
    (forall (l1 : list A),
    (forall (l2 : list A), length l2 < length l1 -> P l2) -> P l1) ->
    forall (l : list A),  P l.
```

`list_length_induction`: 对列表长度进行归纳，但归纳的目标是一个集合，属于构造性的归纳。

```
Definition list_length_induction: forall (P : list A ->  Set),
    (forall (l1 : list A),
    (forall (l2 : list A), length l2 < length l1 -> P l2) -> P l1) ->
    forall (l : list A), P l.
```