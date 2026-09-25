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

def adjacent (u v : G.V) : Prop := ∃ e, u = G.src e ∧ G.dst e = v

def Reachable := Relation.TransGen G.adjacent

example {u v w : G.V} : Reachable u v → Reachable v w → Reachable u w := Relation.TransGen.trans

class DAG (G : Graph) extends Std.Asymm G.Reachable

example [DAG G] : Std.Irrefl G.Reachable := Std.instIrreflOfAsymm G.Reachable

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

theorem Reachable.toRelation {u v : V} : (ofRelation r).Reachable u v → r u v
  | .single ⟨e, p, q⟩ => trans (trans p e.property) q
  | .tail p ⟨e, q, rfl⟩ => trans (trans (toRelation p) q) e.property

instance [Std.Asymm r] : DAG (ofRelation r) where
  asymm u v p q := Std.Asymm.asymm u v p.toRelation q.toRelation

example [lt : LT V] [LE V] [Std.LawfulOrderLT V] [Std.IsPreorder V] : DAG (ofRelation lt.lt) :=
  inferInstance

end

end Graph

/-- Order `n` is ther number of vertices. Size `m` is the number of edges. -/
structure FinGraph (n m : Nat) where
  adjList : Vector (List (Fin n)) n
  size_adjList : (adjList.map List.length).sum = m

namespace FinGraph

variable {n m : Nat}

def toRelation (G : FinGraph n m) (u v : Fin n) : Prop := v ∈ G.adjList.get u

def toGraph (G : FinGraph n m) : Graph := .ofRelation G.toRelation

def addEdge (adjList : Vector (List (Fin n)) n) : Fin n × Fin n → Vector (List (Fin n)) n
  | (u, v) => adjList.set u (v :: adjList.get u)

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
      let vs := adjList.get u
      let k := vs.length
      let ks := adjList.map List.length
      have : ks.get u = k := Vector.getElem_map List.length u.isLt
      have :=
        calc k + (ks.set u k.succ).sum
         _ = ks.get u + (ks.set u k.succ).sum := congrArg (· + _) this.symm
         _ = k + 1 + ks.sum := ks.get_add_set_sum
         _ = k + ks.sum + 1 := k.succ_add _
      calc ((adjList.set u (v :: vs)).map List.length).sum
       _ = (ks.set u k.succ).sum := congrArg Vector.sum Vector.map_set
       _ = ks.sum + 1 := k.add_left_cancel this
       _ = i + 1 := congrArg Nat.succ h
    trans (edges.toArray.foldl_induction motive h0 hf) edges.size_toArray

end FinGraph
