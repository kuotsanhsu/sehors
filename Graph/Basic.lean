structure Graph.{v, e} where
  V : Sort v
  E : Sort e
  (src dst : E → V)

/-- Bollobas, Figure 1.1
```
    2'
 /     \
1 0 - 2 0
|  \ /  |
0'  1   1'
  \   /
    2
```
-/
example : Graph where
  V := Fin 3 ⊕ Fin 3 ⊕ Fin 3
  E := Fin 3 × Fin 3 ⊕ Fin 3 × Fin 3
  src
    | .inl (u', _) => .inr (.inl u')
    | .inr (u , _) => .inr (.inr u )
  dst
    | .inl (u', 0) => .inl (u' + 0)
    | .inl (u', 1) => .inl (u' + 1)
    | .inl (u', 2) => .inr (.inr (u' + 2))
    | .inr (u , 0) => .inl (u  + 0)
    | .inr (u , 1) => .inl (u  + 1)
    | .inr (u , 2) => .inr (.inl (u  + 2))
