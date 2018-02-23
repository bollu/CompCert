# Proof sketch of the proof that loop reversal works if the affine expr is
indvar.

Remember that we are only handling that loops that look exactly like this:


```C
for(int viv = 0; viv < ub; i++) {
   A[sched (i)] = constant;
}
```

OR


```
for(int viv = 0; viv < ub; i++) {
   A[constant_1] = constant_2;
}
```

Where `sched :: [0..ub - 1] -> [0..ub - 1]`, bijective, thus has
`schedinv :: [0..ub - 1] -> [0..ub - 1]`, such that
`sched . schedinv = schedinv . sched = id`

So now, we claim that loop reversal is legal precisely when the loop
is of the first form.


We need the lemmas:

1. Every loop iteration accesses a different index.
   - i is different every index
   - sched is injective.
   - Thus, `i <> i' -> sched(i) <> sched(i')`,
     `sched(i) = sched(i') -> i = i'`

2. If memory is accessed in a range outside that
   touched by the loop, then it will trivially be equal.

3. If memory is accessed in a range inside the loop, then the final write to that block of memory is what matters.

4. the original loop l and the new loop l' will have the same writes.

5. The new loop l' will not have two writes at the same memory location.

6. Thus, if memory is accessed in l', we will use the write from l, and this will be the *only* such write to that memory location in l'.


