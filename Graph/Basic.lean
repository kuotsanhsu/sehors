import Graph.Lemmas

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

namespace Graph

variable {G : Graph}

inductive Reachable : G.V → G.V → Prop
  | adj e : Reachable (G.src e) (G.dst e)
  | cons e {w} : Reachable (G.dst e) w → Reachable (G.src e) w

theorem Reachable.trans {u v w: G.V} : Reachable u v → Reachable v w → Reachable u w
  | adj e, q => cons e q
  | cons e p, q => cons e (p.trans q)

def Cyclic (G : Graph) : Prop := ∃ u v : G.V, Reachable u v ∧ Reachable v u

class DAG (G : Graph) where
  acyclic : ¬G.Cyclic

section

variable [DAG G]

instance : Std.Asymm G.Reachable where
  asymm u v p q := DAG.acyclic ⟨u, v, p, q⟩

example : Std.Irrefl G.Reachable := Std.instIrreflOfAsymm G.Reachable

end

section

variable {V}

abbrev ofRelation (r : V → V → Prop) : Graph where
  V
  E := Subtype (Function.uncurry r)
  src e := e.val.fst
  dst e := e.val.snd

/-- ofFunction -/
example (f : V → V) : Graph := ofRelation (f · = ·)

variable {r : V → V → Prop} [Trans r r r]

theorem Reachable.toRelation {u v : V} : (ofRelation r).Reachable u v → r u v :=
  letI G := ofRelation r
  fun
  | @adj G e => e.property
  | @cons G e _ p => Trans.trans e.property p.toRelation

instance [Std.Asymm r] : DAG (ofRelation r) where
  acyclic | ⟨u, v, p, q⟩ => Std.Asymm.asymm u v p.toRelation q.toRelation

example [lt : LT V] [LE V] [Std.LawfulOrderLT V] [Std.IsPreorder V] : DAG (ofRelation lt.lt) :=
  inferInstance

end

end Graph

/-- Order `n` is ther number of vertices. Size `m` is the number of edges. -/
structure FinGraph (n m : Nat) where
  adjList : Vector (List (Fin n)) n
  size_adjList : (adjList.map List.length).sum = m

#check Vector.size_toArray
example {n} {xs : Vector Nat n} : xs.sum = xs.toArray.foldr (· + ·) 0 := rfl

namespace FinGraph

variable {n m : Nat}

def toRelation (G : FinGraph n m) (u v : Fin n) : Prop := v ∈ G.adjList[u]

def toGraph (G : FinGraph n m) : Graph := .ofRelation G.toRelation

private def addEdge (adjList : Vector (List (Fin n)) n) : Fin n × Fin n → Vector (List (Fin n)) n
  | (u, v) => adjList.set u (v :: adjList[u])

def fromEdges (edges : Vector (Fin n × Fin n) m) : FinGraph n m where
  adjList := edges.foldl addEdge default
  size_adjList :=
    let AdjList := Vector (List (Fin n)) n
    let motive (i : Nat) (adjList : AdjList) := (adjList.map List.length).sum = i
    let init : AdjList := default
    have h0 : (init.map List.length).sum = 0 := by simp [init, default]
    have hf (i : Fin edges.toArray.size) (adjList : AdjList) (h : (adjList.map List.length).sum = i) :
        ((addEdge adjList edges[i]).map List.length).sum = i + 1 :=
      let (u, v) := edges[i]
      let xs := adjList[u]
      let ys := v :: xs
      let p := xs.length
      let q := ys.length
      let as := adjList.map List.length
      have : as.get u = p := Vector.getElem_map List.length u.isLt
      have :=
        calc p + (as.set u q).sum
         _ = as.get u + (as.set u q).sum := congrArg (· + _) this.symm
         _ = q + as.sum := as.get_add_set_sum
         _ = p + 1 + i := congrArg q.add h
         _ = p + i + 1 := Nat.succ_add ..
      calc ((adjList.set u ys).map List.length).sum
       _ = (as.set u q).sum := congrArg Vector.sum Vector.map_set
       _ = i + 1 := Nat.add_left_cancel this
    trans (edges.toArray.foldl_induction motive h0 hf) edges.size_toArray

end FinGraph
