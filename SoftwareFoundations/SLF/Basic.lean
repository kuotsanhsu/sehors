import SoftwareFoundations.SLF.StdExtra
set_option linter.constructorNameAsVariable false
/-
Does not cover CFML which applies separation logic to reasoning about OCaml programs.
Prerequisites: volume 1, Hoare and Hoare2 from volume 2.
-/

section LibSepReference

abbrev Loc := Nat

inductive Var
  | a | b | f | i | j | m | n | p | q | r | s | v | x | y
deriving DecidableEq

mutual
inductive Val
  | unit
  | bool : Bool → Val
  | int : Int → Val
  | loc : Loc → Val
  | fun : Var → Trm → Val
  | fix : Var → Var → Trm → Val

inductive Trm
  | val : Val → Trm
  | var : Var → Trm
  | fun : Var → Trm → Trm
  | fix : Var → Var → Trm → Trm
  | app : Trm → Trm → Trm
  | seq : Trm → Trm → Trm
  | let : Var → Trm → Trm → Trm
  | if  : Trm → Trm → Trm → Trm
  -- Prim
  | get (p : Trm) : Trm
  | set (p v : Trm) : Trm
  | ref (v : Trm) : Trm
  | free (p : Trm) : Trm
  | add : Trm → Trm → Trm
  | sub : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  | eq  : Trm → Trm → Trm
  | ne  : Trm → Trm → Trm
  | le  : Trm → Trm → Trm
  | lt  : Trm → Trm → Trm
  | ge  : Trm → Trm → Trm
  | gt  : Trm → Trm → Trm
  | rand : Trm → Trm
end

instance : Coe Unit Val where coe _ := Val.unit
instance : Coe Bool Val where coe := Val.bool
instance : Coe Int Val where coe := Val.int
instance : Coe Loc Val where coe := Val.loc
instance : Coe Val Trm where coe := Trm.val
instance : Coe Var Trm where coe := Trm.var

abbrev Heap := Std.ExtTreeMap Loc Val
namespace Heap

export Std.ExtTreeMap (
  union_comm_of_disjoint
  union_assoc
  mem_union_of_left
  mem_union_of_right
  mem_union_iff
  not_mem_empty
)

variable {s : Heap} {p : Loc} {v w : Val}
example : ∅ ∪ ∅ = (∅ : Heap) := rfl
example (p : Loc) (v : Val) : {(p, v)} ∪ ∅ = ({(p, v)} : Heap) := rfl
example (p : Loc) (v : Val) : ∅ ∪ {(p, v)} = ({(p, v)} : Heap) := rfl
theorem erase_of_insert : (s.insert p v).erase p = s.erase p :=
  Std.ExtTreeMap.ext_getElem? fun k =>
    let c := compare p k = .eq
    calc ((s.insert p v).erase p)[k]?
     _ = if c then none else (s.insert p v)[k]? := Std.ExtTreeMap.getElem?_erase
     _ = if c then none else s[k]? := ite_congr rfl (fun _ => rfl) fun h =>
      calc (s.insert p v)[k]?
       _ = if c then some v else s[k]? := Std.ExtTreeMap.getElem?_insert
       _ = s[k]? := ite_eq_right h
     _ = (s.erase p)[k]? := Std.ExtTreeMap.getElem?_erase.symm
theorem singleton_mem : p ∈ ({(p, v)} : Heap) :=
  Std.ExtTreeMap.mem_insert_self
theorem singleton_get : ({(p, v)} : Heap).get p singleton_mem = v :=
  Std.ExtTreeMap.getElem_insert_self
theorem singleton_insert : ({(p, v)} : Heap).insert p w = {(p, w)} :=
  Std.ExtTreeMap.ext_getElem? fun k =>
    let s : Heap := ∅
    let t : Heap := {(p, v)}
    calc (t.insert p w)[k]?
     _ = if _ then some w else t[k]? := t.getElem?_insert
     _ = if _ then some w else s[k]? := ite_congr rfl (fun _ => rfl) fun hn =>
      calc t[k]?
       _ = if _ then some v else s[k]? := s.getElem?_insert
       _ = s[k]? := ite_eq_right hn
     _ = {(p, w)}[k]? := s.getElem?_insert.symm
theorem singleton_erase : ({(p, v)} : Heap).erase p = ∅ :=
  erase_of_insert.trans rfl
theorem singleton_inj (h : @Eq Heap {(p, v)} {(p, w)}) : v = w :=
  Option.some.inj <|
    calc some v
     _ = ({(p, v)} : Heap)[p]? := Std.ExtTreeMap.getElem?_insert_self.symm
     _ = ({(p, w)} : Heap)[p]? := h.rec rfl
     _ = some w := Std.ExtTreeMap.getElem?_insert_self

variable {s₁ s₂ : Heap}
theorem union_insert_right : (s₁ ∪ s₂).insert p v = s₁ ∪ s₂.insert p v :=
  Std.ExtTreeMap.union_insert_right_eq_insert_union (p := ⟨p, v⟩) |>.symm
theorem union_insert_left (m₂ : p ∉ s₂) : (s₁ ∪ s₂).insert p v = s₁.insert p v ∪ s₂ :=
  Std.ExtTreeMap.ext_getElem? fun k =>
    let c := compare p k = .eq
    let v' := some v
    calc ((s₁ ∪ s₂).insert p v)[k]?
     _ = if c then v' else (s₁ ∪ s₂)[k]? := (s₁ ∪ s₂).getElem?_insert
     _ = if c then v' else s₂[k]?.or s₁[k]? := congrArg _ Std.ExtTreeMap.getElem?_union
     _ = s₂[k]?.or (if c then some v else s₁[k]?) := Eq.symm <|
      if e : c then
        have : p = k := Std.LawfulEqCmp.eq_of_compare e
        calc s₂[k]?.or (if c then v' else _)
         _ = s₂[k]?.or v' := congrArg _ (ite_eq_left e)
         _ = none.or v' := congrArg (Option.or · v') <| this.rec (s₂.getElem?_eq_none m₂)
         _ = if c then v' else _ := (ite_eq_left e).symm
      else
        calc s₂[k]?.or (if c then _ else s₁[k]?)
         _ = s₂[k]?.or s₁[k]? := congrArg _ (ite_eq_right e)
         _ = if c then _ else s₂[k]?.or s₁[k]? := (ite_eq_right e).symm
     _ = s₂[k]?.or (s₁.insert p v)[k]? := congrArg _ s₁.getElem?_insert.symm
     _ = (s₁.insert p v ∪ s₂)[k]? := Std.ExtTreeMap.getElem?_union.symm
theorem union_get_right (m₂ : p ∈ s₂) : (s₁ ∪ s₂).get p (mem_union_of_right m₂) = s₂.get p m₂ :=
  Std.ExtTreeMap.getElem_union_of_mem_right m₂
theorem union_get_left (m₁ : p ∈ s₁) (m₂ : p ∉ s₂) : (s₁ ∪ s₂).get p (mem_union_of_left m₁) = s₁.get p m₁ :=
  Option.some.inj <|
    calc some ((s₁ ∪ s₂).get p (mem_union_of_left m₁))
    _ = (s₁ ∪ s₂)[p]? := (s₁ ∪ s₂).getElem?_eq_some_getElem _ |>.symm
    _ = s₁[p]? := s₁.getElem?_union_of_not_mem_right m₂
    _ = some (s₁.get p m₁) := s₁.getElem?_eq_some_getElem _
theorem empty_disjoint : Disjoint ∅ s₂
  | _, m₁, _ => nomatch m₁
theorem disjoint_empty : Disjoint s₁ ∅ :=
  s₁.empty_disjoint.symm
theorem insert_disjoint (h : Disjoint s₁ s₂) (m₁ : p ∈ s₁) : Disjoint (s₁.insert p v) s₂
  | q, (m₁' : q ∈ s₁.insert p v), (m₂ : q ∈ s₂) =>
    match s₁.mem_insert.mp m₁' with
    | .inl e => h p m₁ (Std.LawfulEqCmp.eq_of_compare e |>.symm.subst m₂)
    | .inr m₁' => h q m₁' m₂
theorem disjoint_insert (h : Disjoint s₁ s₂) (m₂ : p ∈ s₂) : Disjoint s₁ (s₂.insert p v) :=
  insert_disjoint h.symm m₂ |>.symm
theorem erase_disjoint (h : Disjoint s₁ s₂) : Disjoint (s₁.erase p) s₂
  | q, m₁, m₂ => h q (s₁.mem_of_mem_erase m₁) m₂
theorem disjoint_erase (h : Disjoint s₁ s₂) : Disjoint s₁ (s₂.erase p) :=
  erase_disjoint h.symm |>.symm

theorem erase_of_not_mem (m : p ∉ s) : s.erase p = s :=
  Std.ExtTreeMap.ext_getElem? fun k =>
    let c := compare p k = .eq
    calc (s.erase p)[k]?
     _ = if c then none else s[k]? := s.getElem?_erase
     _ = s[k]? :=
      if e : c then
        calc if c then none else _
         _ = none := ite_eq_left e
         _ = s[p]? := s.getElem?_eq_none m |>.symm
         _ = s[k]? := Std.ExtTreeMap.getElem?_congr e
      else
        ite_eq_right e
theorem union_erase : (s₁ ∪ s₂).erase p = s₁.erase p ∪ s₂.erase p :=
  Std.ExtTreeMap.ext_getElem? fun k =>
    let c := compare p k = .eq
    let f (v : Option Val) := if c then none else v
    let g (s : Heap) := f s[k]?
    calc ((s₁ ∪ s₂).erase p)[k]?
     _ = g (s₁ ∪ s₂) := (s₁ ∪ s₂).getElem?_erase
     _ = f (s₂[k]?.or s₁[k]?) := congrArg f Std.ExtTreeMap.getElem?_union
     _ = (g s₂).or (g s₁) := Eq.symm <|
      if e : c then
        calc (g s₂).or (g s₁)
         _ = (g s₂).or none := congrArg _ (ite_eq_left e)
         _ = none.or none := congrArg (Option.or · none) (ite_eq_left e)
         _ = f (s₂[k]?.or s₁[k]?) := (ite_eq_left e).symm
      else
        calc (g s₂).or (g s₁)
         _ = (g s₂).or s₁[k]? := congrArg _ (ite_eq_right e)
         _ = s₂[k]?.or s₁[k]? := congrArg (Option.or · s₁[k]?) (ite_eq_right e)
         _ = f (s₂[k]?.or s₁[k]?) := (ite_eq_right e).symm
     _ = (s₂.erase p)[k]?.or (s₁.erase p)[k]? := by rw [s₁.getElem?_erase, s₂.getElem?_erase]
     _ = (s₁.erase p ∪ s₂.erase p)[k]? := Std.ExtTreeMap.getElem?_union.symm
theorem union_erase_right (m₁ : p ∉ s₁) : (s₁ ∪ s₂).erase p = s₁ ∪ s₂.erase p :=
  calc (s₁ ∪ s₂).erase p
   _ = s₁.erase p ∪ s₂.erase p := union_erase
   _ = s₁ ∪ s₂.erase p := congrArg (· ∪ _) (erase_of_not_mem m₁)
theorem union_erase_left (m₂ : p ∉ s₂) : (s₁ ∪ s₂).erase p = s₁.erase p ∪ s₂ :=
  calc (s₁ ∪ s₂).erase p
   _ = s₁.erase p ∪ s₂.erase p := union_erase
   _ = s₁.erase p ∪ s₂ := congrArg _ (erase_of_not_mem m₂)

theorem getElem?_singleton_eq_some : ({(p, v)} : Heap)[p]? = some v :=
  Std.ExtTreeMap.getElem?_insert_self
theorem getElem?_singleton_eq_none {k} (h : p ≠ k) : ({(p, v)} : Heap)[k]? = none :=
  suffices k ∉ {(p, v)} from Std.ExtTreeMap.getElem?_eq_none this
  fun m =>
    suffices k ∈ ∅ from Std.ExtTreeMap.not_mem_empty this
    Std.ExtTreeMap.mem_of_mem_insert m (h ∘ Std.LawfulEqCmp.eq_of_compare)
theorem union_singleton_of_insert : s.insert p v = s ∪ {(p, v)} :=
  let s' : Heap := {(p, v)}
  Std.ExtTreeMap.ext_getElem? fun k =>
    let c := compare p k = .eq
    let w' := s'[k]?
    let w := s[k]?
    calc (s.insert p v)[k]?
     _ = if c then some v else w := s.getElem?_insert
     _ = w'.or w :=
      if e : c then
        calc if c then some v else w
         _ = some v := ite_eq_left e
         _ = (some v).or w := rfl
         _ = s'[p]?.or w := congrArg (Option.or · w) Std.ExtTreeMap.getElem?_insert_self.symm
         _ = w'.or w := congrArg (Option.or · w) (Std.ExtTreeMap.getElem?_congr e)
      else
        have : p ≠ k := e ∘ Nat.compare_eq_eq.mpr
        calc if c then some v else w
         _ = w := ite_eq_right e
         _ = none.or w := rfl
         _ = w'.or w := congrArg (Option.or · w) (getElem?_singleton_eq_none this).symm
     _ = (s ∪ s')[k]? := Std.ExtTreeMap.getElem?_union.symm
theorem eq_of_mem_singleton {k} (h : k ∈ ({(p, v)} : Heap)) : p = k :=
  match Std.ExtTreeMap.mem_insert.mp h with
  | .inl e => Std.LawfulEqCmp.eq_of_compare e
  | .inr m => Std.ExtTreeMap.not_mem_empty m |>.rec

end Heap

def HProp := Heap → Prop

namespace HProp

variable {α}

def himpl (H₁ H₂ : HProp) : Prop := ∀ h, H₁ h → H₂ h
def qimpl (Q₁ Q₂ : α → HProp) : Prop := ∀ x, (Q₁ x).himpl (Q₂ x)
def hempty : HProp | h => h = ∅
/-- `p ~~> n`: the contents of the location `p` is the value `n` -/
def hsingle (p : Loc) (v : Val) : HProp | h => h = {(p, v)}
def hstar (H₁ H₂ : HProp) : HProp | h => ∃ h₁ h₂, H₁ h₁ ∧ H₂ h₂ ∧ Disjoint h₁ h₂ ∧ h = h₁ ∪ h₂
instance : Mul HProp where mul := hstar
def hexists (Q : α → HProp) : HProp | h => ∃ x, Q x h
def hforall (Q : α → HProp) : HProp | h => ∀ x, Q x h
def hpure (P : Prop) : HProp := hexists fun _ : P => hempty
def htop : HProp := hexists id
def hwand (H₁ H₂ : HProp) : HProp := hexists fun H₀ => H₀ * (hpure <| (H₁ * H₀).himpl H₂)
def qwand (Q₁ Q₂ : α → HProp) : HProp := hforall fun x => (Q₁ x).hwand (Q₂ x)
def funval (toVal : α → Val) (Q : α → HProp) (r : Val) : HProp := hexists fun x => hpure (r = toVal x) * Q x
abbrev funloc := funval Val.loc
abbrev funint := funval Val.int

variable {H H₁ H₂ H₃ : HProp} {op : HProp → HProp → HProp} {Q : α → HProp} {h h₁ h₂ : Heap}

theorem himpl.rfl : H.himpl H
  | _ => id
theorem himpl.trans : H₁.himpl H₂ → H₂.himpl H₃ → H₁.himpl H₃
  | p, q, h => q h ∘ p h
theorem himpl.antisymm : H₁.himpl H₂ → H₂.himpl H₁ → H₁ = H₂
  | p, q => funext fun h => propext ⟨p h, q h⟩
theorem himpl.comm (p : ∀ H₁ H₂, (op H₁ H₂).himpl (op H₂ H₁)) : op H₁ H₂ = op H₂ H₁ :=
  (p H₁ H₂).antisymm (p H₂ H₁)
theorem qimpl.rfl : qimpl Q Q
  | _ => .rfl
theorem hempty.intro : hempty ∅ :=
  rfl
theorem hempty.inv : hempty h → h = ∅ :=
  id
theorem hstar.intro : H₁ h₁ → H₂ h₂ → Disjoint h₁ h₂ → (H₁ * H₂) (h₁ ∪ h₂)
  | p₁, p₂, q => ⟨h₁, h₂, p₁, p₂, q, rfl⟩
theorem hstar.inv : (H₁ * H₂) h → ∃ h₁ h₂, H₁ h₁ ∧ H₂ h₂ ∧ Disjoint h₁ h₂ ∧ h = (h₁ ∪ h₂) :=
  id
theorem himpl.hstar (H₁ H₂ : HProp) : (H₁ * H₂).himpl (H₂ * H₁)
  | _, ⟨h₁, h₂, p₁, p₂, q, e⟩ => ⟨h₂, h₁, p₂, p₁, q.symm, e.trans (Heap.union_comm_of_disjoint q)⟩
theorem hstar.comm : H₁ * H₂ = H₂ * H₁ :=
  himpl.comm .hstar
theorem hstar.assoc : H₁ * H₂ * H₃ = H₁ * (H₂ * H₃) :=
  himpl.antisymm
  fun | _, ⟨_, h₃, ⟨h₁, h₂, p₁, p₂, q₁₂, rfl⟩, p₃, q, rfl⟩ =>
      show H₁ * (H₂ * H₃) <| h₁ ∪ h₂ ∪ h₃ from
      suffices H₁ * (H₂ * H₃) <| h₁ ∪ (h₂ ∪ h₃) from Heap.union_assoc.symm.subst this
      have q₂₃ : Disjoint h₂ h₃ := fun x m₂ m₃ => q x (Heap.mem_union_of_right m₂) m₃
      have q' : Disjoint h₁ (h₂ ∪ h₃) := fun x m₁ m₂₃ =>
        (Heap.mem_union_iff.mp m₂₃).rec (q₁₂ x m₁) (q x (Heap.mem_union_of_left m₁))
      ⟨h₁, _, p₁, ⟨h₂, h₃, p₂, p₃, q₂₃, rfl⟩, q', rfl⟩
  fun | _, ⟨h₁, _, p₁, ⟨h₂, h₃, p₂, p₃, q₂₃, rfl⟩, q', rfl⟩ =>
      show H₁ * H₂ * H₃ <| h₁ ∪ (h₂ ∪ h₃) from
      suffices H₁ * H₂ * H₃ <| h₁ ∪ h₂ ∪ h₃ from Heap.union_assoc.subst this
      have q₁₂ : Disjoint h₁ h₂ := fun x m₁ m₂ => q' x m₁ (Heap.mem_union_of_left m₂)
      have q : Disjoint (h₁ ∪ h₂) h₃ := fun x m₁₂ m₃ =>
        (Heap.mem_union_iff.mp m₁₂).rec (q' x · (Heap.mem_union_of_right m₃)) (q₂₃ x · m₃)
      ⟨_, h₃, ⟨h₁, h₂, p₁, p₂, q₁₂, rfl⟩, p₃, q, rfl⟩
theorem hempty_hstar : hempty.hstar H = H :=
  himpl.antisymm
  fun | _, ⟨_, h, rfl, p, _, rfl⟩ => h.empty_union.symm.subst p
  fun | h, p => ⟨_, h, rfl, p, (fun _ m _ => nomatch m), h.empty_union.symm⟩
theorem hstar_hempty : H * hempty = H :=
  hstar.comm.trans hempty_hstar
theorem hstar_hexists : hexists Q * H = hexists fun x => Q x * H :=
  himpl.antisymm
  fun | _, ⟨s₁, s₂, ⟨x, h₁⟩, rest⟩ => ⟨x, s₁, s₂, h₁, rest⟩
  fun | _, ⟨x, s₁, s₂, h₁, rest⟩ => ⟨s₁, s₂, ⟨x, h₁⟩, rest⟩
theorem hexists_hstar : H * hexists Q = hexists fun x => H * Q x :=
  calc H * hexists Q
   _ = hexists Q * H := hstar.comm
   _ = hexists fun x => Q x * H := hstar_hexists
   _ = hexists fun x => H * Q x := congrArg hexists <| funext fun _ => hstar.comm
theorem funloc_hstar {Q r} : funloc Q r * H = funloc (fun p => Q p * H) r :=
  calc funloc Q r * H
   _ = hexists fun p : Loc => hpure (r = p) * Q p * H := hstar_hexists
   _ = hexists fun p : Loc => hpure (r = p) * (Q p * H) := congrArg hexists <| funext fun _ => hstar.assoc
theorem hstar_funloc {Q r} : H * funloc Q r = funloc (fun p => H * Q p) r :=
  calc H * funloc Q r
   _ = funloc Q r * H := hstar.comm
   _ = funloc (fun p => Q p * H) r := funloc_hstar
   _ = funloc (fun p => H * Q p) r := congrArg (funloc · r) <| funext fun _ => hstar.comm

end HProp

namespace Trm

def IsVal : Trm → Prop
  | val _ => True
  | _ => False

variable (y : Var) (v : Val)
/-- Substitute the variable `y` with the value `v` in the term `t`. -/
def subst : Trm → Trm
  | t@(val _) => t
  | t@(var x) => if x = y then v else t
  | t@(.fun x body) => if x = y then t else .fun x body.subst
  | t@(fix f x body) => if f = y ∨ x = y then t else fix f x body.subst
  | app fn arg => app fn.subst arg.subst
  | .let x rhs scope => .let x rhs.subst <| if x = y then scope else scope.subst
  | .if c t f => .if c.subst t.subst f.subst
  | seq fst snd => seq fst.subst snd.subst
  -- Prim
  |  get p   =>  get p.subst
  |  set p v =>  set p.subst v.subst
  |  ref   v =>  ref         v.subst
  | free p   => free p.subst
  | add lhs rhs => add lhs.subst rhs.subst
  | sub lhs rhs => sub lhs.subst rhs.subst
  | mul lhs rhs => mul lhs.subst rhs.subst
  | eq  lhs rhs => eq  lhs.subst rhs.subst
  | ne  lhs rhs => ne  lhs.subst rhs.subst
  | le  lhs rhs => le  lhs.subst rhs.subst
  | lt  lhs rhs => lt  lhs.subst rhs.subst
  | ge  lhs rhs => ge  lhs.subst rhs.subst
  | gt  lhs rhs => gt  lhs.subst rhs.subst
  | rand t => rand t.subst

end Trm

/-!
## Omni-Big-Step Semantics
-/

inductive Eval : (Val → HProp) → Trm → HProp
  | val      {     s Q}   {v : Val} :        Q  v             s  → Eval Q  v                     s
  | add      {     s Q} {m n : Int} :        Q (m + n)        s  → Eval Q (.add m n)             s
  | sub      {     s Q} {m n : Int} :        Q (m - n)        s  → Eval Q (.sub m n)             s
  | mul      {     s Q} {m n : Int} :        Q (m * n)        s  → Eval Q (.mul m n)             s
  | eq       {     s Q} {m n : Int} :        Q (m.beq' n)     s  → Eval Q (.eq  m n)             s
  | ne       {     s Q} {m n : Int} :        Q (m.beq' n).not s  → Eval Q (.ne  m n)             s
  | le       {     s Q} {m n : Int} :        Q (m.ble' n)     s  → Eval Q (.le  m n)             s
  | lt       {     s Q} {m n : Int} :        Q (m.blt' n)     s  → Eval Q (.lt  m n)             s
  | ge       {     s Q} {m n : Int} :        Q (n.ble' m)     s  → Eval Q (.ge  m n)             s
  | gt       {     s Q} {m n : Int} :        Q (n.blt' m)     s  → Eval Q (.gt  m n)             s
  | rand {s Q} {n : Int} : n > 0 → (∀ m : Int, 0 ≤ m → m < n → Q m s) → Eval Q (.rand n) s
  | fun      {t    s Q x}           :        Q (.fun   x   t) s  → Eval Q (.fun x t)             s
  | fix      {t f  s Q x}           :        Q (.fix f x   t) s  → Eval Q (.fix f x t)           s
  | if       {t f  s Q}   {c : Bool}:   Eval Q (cond c t f)   s  → Eval Q (.if c t f)            s
  | app_fun  {t    s Q x} {v : Val} :   Eval Q (.subst x v t) s  → Eval Q (.app (Val.fun x t) v) s
  | app_fix  {t f  s Q x} {v : Val} :
    Eval Q (.subst x v (.subst f (.fix f x t) t)) s → Eval Q (.app (Val.fix f x t) v) s
  | app₁ Q'  {t t' s Q} (hn : ¬t'.IsVal) :
    Eval Q'     t' s → (∀ v s, Q' v s → Eval Q (.app     v t) s) → Eval Q (.app   t' t)          s
  | app₂ Q'  {t    s Q} {f : Val} (hn : ¬t.IsVal) :
    Eval Q'   t    s → (∀ v s, Q' v s → Eval Q (.app   f v  ) s) → Eval Q (.app f    t)          s
  | let  Q'  {t t' s Q x} :
    Eval Q'     t' s → (∀ v s, Q' v s → Eval Q (.subst x v t) s) → Eval Q (.let x t' t)          s
  | seq  Q'  {t t' s Q} :
    Eval Q'     t' s → (∀ v s, Q' v s → Eval Q             t  s) → Eval Q (.seq   t' t)          s
  | get {p : Loc} {s Q} (m : p ∈ s) :        Q (s.get p m)    s  → Eval Q (.get p)               s
  | set {p : Loc} {s Q} (m : p ∈ s) {v : Val} : Q () (s.insert p v) → Eval Q (.set p v)          s
  | ref           {s Q}             {v : Val} : (∀ p ∉ s, Q p (s.insert p v)) → Eval Q (.ref v)  s
  | free{p : Loc} {s Q} (m : p ∈ s) :        Q () (s.erase p)    → Eval Q (.free p)              s

namespace Eval

theorem frame₁ {s₁ s₂ t Q H₂} (q : Disjoint s₁ s₂) (h₂ : H₂ s₂) : Eval Q t s₁ → Eval (fun v => Q v * H₂) t (s₁ ∪ s₂)
  |  val h₁ =>  val ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |  add h₁ =>  add ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |  sub h₁ =>  sub ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |  mul h₁ =>  mul ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |   eq h₁ =>   eq ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |   ne h₁ =>   ne ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |   le h₁ =>   le ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |   lt h₁ =>   lt ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |   ge h₁ =>   ge ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |   gt h₁ =>   gt ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  | .fun h₁ => .fun ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |  fix h₁ =>  fix ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  | rand hn h => rand hn fun m hge hlt => ⟨s₁, s₂, h m hge hlt, h₂, q, rfl⟩
  | .if       e₁   => .if       (e₁.frame₁ q h₂)
  | app_fun   e₁   => app_fun   (e₁.frame₁ q h₂)
  | app_fix   e₁   => app_fix   (e₁.frame₁ q h₂)
  | app₁ _ hn e₁ h => app₁ _ hn (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | app₂ _ hn e₁ h => app₂ _ hn (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | .let _    e₁ h => .let _    (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | seq  _    e₁ h => seq  _    (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | get m₁ h₁ => get (Heap.mem_union_of_left m₁) ⟨s₁, s₂, Heap.union_get_left m₁ (q _ m₁) |>.symm.rec h₁, h₂, q, rfl⟩
  | set m₁ h₁ => set (Heap.mem_union_of_left m₁) ⟨_, s₂, h₁, h₂, Heap.insert_disjoint q m₁, Heap.union_insert_left (q _ m₁)⟩
  | ref h => ref fun p m =>
    ⟨s₁.insert p _, s₂, h p fun m₁ => m (Heap.mem_union_of_left m₁), h₂, {
      right := Heap.union_insert_left fun m₂ => m (Heap.mem_union_of_right m₂)
      left r m₁' m₂ := suffices r ∈ s₁ from q r this m₂
        match r.decEq p with
        | isTrue rfl => m (Heap.mem_union_of_right m₂) |>.rec
        | isFalse hn => s₁.mem_of_mem_insert m₁' fun e => hn (Std.LawfulEqCmp.eq_of_compare e).symm
    }⟩
  | free m₁ h₁ => free (Heap.mem_union_of_left m₁) ⟨_, s₂, h₁, h₂, Heap.erase_disjoint q, Heap.union_erase_left (q _ m₁)⟩
theorem frame₂ {s₁ s₂ t Q H₁} (q : Disjoint s₁ s₂) (h₁ : H₁ s₁) : Eval Q t s₂ → Eval (fun v => H₁ * Q v) t (s₁ ∪ s₂)
  | e₂ => by
    conv => arg 1; ext; rw [HProp.hstar.comm]
    rw [Heap.union_comm_of_disjoint q]
    show Eval (fun v => Q v * H₁) t (s₂ ∪ s₁)
    exact e₂.frame₁ q.symm h₁
theorem eventually {s t Q} : Eval Q t s → ∃ v s, Q v s
  |  val       h
  |  add       h
  |  sub       h
  |  mul       h
  |   eq       h
  |   ne       h
  |   le       h
  |   lt       h
  |   ge       h
  |   gt       h
  | .fun       h
  |  fix       h
  |  get _     h
  |  set _     h
  | free _     h => ⟨_, _, h⟩
  | rand (n := n) hn h => ⟨_, s, h 0 ⟨0⟩ hn⟩
  | ref (v := v) h =>
    match e : s.maxKey? with
    | none =>
      have p : Loc := 0
      have : s = ∅ := s.maxKey?_eq_none_iff.mp e
      ⟨p, _, h p <| s.eq_empty_iff_forall_not_mem.mp this p⟩
    | some pmax =>
      have ⟨_, hle⟩ := s.maxKey?_eq_some_iff_mem_and_forall.mp e
      let p : Loc := pmax + 1
      have hgt : pmax < p := p.le_refl
      ⟨p, _, h p fun m : p ∈ s => Nat.not_le_of_gt hgt (p.isLE_compare.mp (hle p m) : p ≤ pmax)⟩
  | app₁ _ _ e h
  | app₂ _ _ e h
  | .let   _ e h
  |  seq   _ e h => match e.eventually with | ⟨v, s, q⟩ => (h v s q).eventually
  |      .if e
  |  app_fun e
  |  app_fix e => e.eventually
theorem and {s t Q₁ Q₂} : Eval Q₁ t s → Eval Q₂ t s → Eval (fun v s => Q₁ v s ∧ Q₂ v s) t s
  |   val h₁,   val h₂ =>   val ⟨h₁, h₂⟩
  |   add h₁,   add h₂ =>   add ⟨h₁, h₂⟩
  |   sub h₁,   sub h₂ =>   sub ⟨h₁, h₂⟩
  |   mul h₁,   mul h₂ =>   mul ⟨h₁, h₂⟩
  |    eq h₁,    eq h₂ =>    eq ⟨h₁, h₂⟩
  |    ne h₁,    ne h₂ =>    ne ⟨h₁, h₂⟩
  |    le h₁,    le h₂ =>    le ⟨h₁, h₂⟩
  |    lt h₁,    lt h₂ =>    lt ⟨h₁, h₂⟩
  |    ge h₁,    ge h₂ =>    ge ⟨h₁, h₂⟩
  |    gt h₁,    gt h₂ =>    gt ⟨h₁, h₂⟩
  |  .fun h₁,  .fun h₂ =>  .fun ⟨h₁, h₂⟩
  |   fix h₁,   fix h₂ =>   fix ⟨h₁, h₂⟩
  | get m h₁, get _ h₂ => get m ⟨h₁, h₂⟩
  | set m h₁, set _ h₂ => set m ⟨h₁, h₂⟩
  |free m h₁,free _ h₂ =>free m ⟨h₁, h₂⟩
  |rand h h₁,rand _ h₂ =>rand h fun m hge hlt => ⟨h₁ m hge hlt, h₂ m hge hlt⟩
  |   ref h₁,   ref h₂ => ref fun p m => ⟨h₁ p m, h₂ p m⟩
  |     .if e₁,     .if e₂ =>     .if (e₁.and e₂)
  | app_fun e₁, app_fun e₂ => app_fun (e₁.and e₂)
  | app_fix e₁, app_fix e₂ => app_fix (e₁.and e₂)
  | app₁ _ hn e₁ k₁, app₁ _ _ e₂ k₂ => app₁ _ hn (e₁.and e₂) fun v s ⟨h₁, h₂⟩ => (k₁ v s h₁).and (k₂ v s h₂)
  | app₂ _ hn e₁ k₁, app₂ _ _ e₂ k₂ => app₂ _ hn (e₁.and e₂) fun v s ⟨h₁, h₂⟩ => (k₁ v s h₁).and (k₂ v s h₂)
  | .let _    e₁ k₁, .let   _ e₂ k₂ => .let _    (e₁.and e₂) fun v s ⟨h₁, h₂⟩ => (k₁ v s h₁).and (k₂ v s h₂)
  |  seq _    e₁ k₁,  seq   _ e₂ k₂ =>  seq _    (e₁.and e₂) fun v s ⟨h₁, h₂⟩ => (k₁ v s h₁).and (k₂ v s h₂)
  | app₁ _ hn .., app_fun _ | app_fun _, app₁ _ hn ..
  | app₂ _ hn .., app_fun _ | app_fun _, app₂ _ hn ..
  | app₁ _ hn .., app_fix _ | app_fix _, app₁ _ hn ..
  | app₂ _ hn .., app_fix _ | app_fix _, app₂ _ hn ..
  | app₁ _ hn .., app₂ ..   | app₂ ..  , app₁ _ hn .. => (hn trivial).rec
theorem and_eventually {s t Q₁ Q₂} : Eval Q₁ t s → Eval Q₂ t s → ∃ v s, Q₁ v s ∧ Q₂ v s
  | e₁, e₂ => (e₁.and e₂).eventually
theorem conseq {s t Q₁ Q₂} (hq : ∀ v s, Q₁ v s → Q₂ v s) : Eval Q₁ t s → Eval Q₂ t s
  | val   h =>  val   (hq _ _ h)
  | add   h =>  add   (hq _ _ h)
  | sub   h =>  sub   (hq _ _ h)
  | mul   h =>  mul   (hq _ _ h)
  |  eq   h =>   eq   (hq _ _ h)
  |  ne   h =>   ne   (hq _ _ h)
  |  le   h =>   le   (hq _ _ h)
  |  lt   h =>   lt   (hq _ _ h)
  |  ge   h =>   ge   (hq _ _ h)
  |  gt   h =>   gt   (hq _ _ h)
  |.fun   h => .fun   (hq _ _ h)
  | fix   h =>  fix   (hq _ _ h)
  | get m h =>  get m (hq _ _ h)
  | set m h =>  set m (hq _ _ h)
  |free m h => free m (hq _ _ h)
  | rand hn h => rand hn fun m hle hgt => hq _ _ (h m hle hgt)
  | ref   h => ref fun p m => hq _ _ (h p m)
  |     .if   e   =>     .if  (e.conseq hq)
  | app_fun   e   => app_fun  (e.conseq hq)
  | app_fix   e   => app_fix  (e.conseq hq)
  | app₁ _ hn e k => app₁ _ hn e fun v s h => (k v s h).conseq hq
  | app₂ _ hn e k => app₂ _ hn e fun v s h => (k v s h).conseq hq
  | .let _    e k => .let _    e fun v s h => (k v s h).conseq hq
  |  seq _    e k =>  seq _    e fun v s h => (k v s h).conseq hq

end Eval

def Triple (t : Trm) (H : HProp) (Q : Val → HProp) := ∀ s, H s → Eval Q t s

end LibSepReference

namespace Trm

instance {n} : OfNat Trm n where ofNat := Val.int n
instance : Add Trm where add := add
instance : Sub Trm where sub := sub
instance : Mul Trm where mul := mul

export Var (a b f i j m n p q r s v x y)

end Trm

/-!
# Basic Proofs in Separation Logic
-/

section Basic

def incr : Val :=
-- fun 'p =>
  .fun .p <|
--   let 'n = !'p in
    .let .n (.get .p) <|
--   let 'm = 'n + 1 in
    .let .m (.n + 1) <|
--   'p := 'm
    .set .p .m

theorem triple_incr (p : Loc) (n : Int) :
  Triple (.app incr p)
    (.hsingle p n)
    fun _ => .hsingle p (n + 1 : Int)
:=
  let s : Heap := {(p, Val.int n)}
  let m : Int := n + 1
  let Q _ : HProp := HProp.hsingle p m
  fun
  | _, rfl => suffices Eval Q (.let .n (.get p) <| .let .m (.n + 1) <| .set p .m) s from .app_fun this
  .let (fun v h => v = n ∧ h = s) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => show Eval Q (.let .m (n + 1) <| .set p .m) s from
  .let (fun v h => v = m ∧ h = s) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => show Eval Q (.set p m) s from
  .set Heap.singleton_mem Heap.singleton_insert

def example_let : Val :=
  .fun .n <|
    .let .a (.n + 1) <|
    .let .b (.n - 1) <|
    .add .a .b

theorem triple_example_let (n : Int) :
  Triple (.app example_let n)
    .hempty
    fun r => .hpure (r = (2 * n : Int))
:=
  let a : Int := n + 1
  let b : Int := n - 1
  fun
  | _, rfl => .app_fun <| .let (fun v h => v = a ∧ h = ∅) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = b ∧ h = ∅) (.sub ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .add ⟨congrArg Val.int (show a + b = 2 * n by lia), rfl⟩

def quadruple : Val :=
  .fun .n <|
    .let .m (.n + .n) <|
    .add .m .m

theorem triple_quadruple (n : Int) :
  Triple (.app quadruple n)
    .hempty
    fun r => .hpure (r = (4 * n: Int))
:=
  let m : Int := n + n
  fun
  | _, rfl => .app_fun <| .let (fun v h => v = m ∧ h = ∅) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .add ⟨congrArg Val.int (show m + m = 4 * n by lia), rfl⟩

def inplace_double : Val :=
  .fun .p <|
    .let .n (.get .p) <|
    .let .m (.n + .n) <|
    .set .p .m

theorem triple_inplace_double (p : Loc) (n : Int) :
  Triple (.app inplace_double p)
    (.hsingle p n)
    fun _ => .hsingle p (2 * n : Int)
:=
  let s : Heap := {(p, Val.int n)}
  let m : Int := n + n
  fun
  | _, rfl => .app_fun <|
  .let (fun v h => v = n ∧ h = s) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = m ∧ h = s) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .set Heap.singleton_mem <| (show m = 2 * n by lia).rec Heap.singleton_insert

def incr_two : Val :=
  .fun .p <| .fun .q <| .seq (.app incr .p) (.app incr .q)

theorem triple_incr_two (p q : Loc) (m n : Int) :
  Triple (.app (.app incr_two p) q)
    (.hsingle p m * .hsingle q n)
    fun _ => .hsingle p (m + 1 : Int) * .hsingle q (n + 1: Int)
:=
  let x : Int := m + 1
  let y : Int := n + 1
  let Q _ : HProp := HProp.hsingle p x * HProp.hsingle q y
  let f : Val := .fun .q <| .seq (.app incr p) (.app incr .q)
  let s₁ : Heap := {(p, Val.int m)}
  let s₂ : Heap := {(q, Val.int n)}
  let s : Heap := s₁ ∪ s₂
  fun
  | _, ⟨_, _, rfl, rfl, h, rfl⟩ => show Eval Q (.app (.app incr_two p) q) s from
  .app₁ (fun v h => v = f ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => show Eval Q (.app f q) s from .app_fun <|
  .seq (fun _ => HProp.hsingle p x * HProp.hsingle q n) (.frame₁ h rfl <| triple_incr p m s₁ rfl) fun
  | _, _, ⟨_, _, rfl, rfl, h, rfl⟩ => show Eval Q (.app incr q) ({(p, Val.int x)} ∪ s₂) from
  .frame₂ h rfl <| triple_incr q n s₂ rfl

theorem triple_incr_two_aliased (p : Loc) (n : Int) :
  Triple (.app (.app incr_two p) p)
    (.hsingle p n)
    fun _ => .hsingle p (n + 2 : Int)
:=
  let s : Heap := {(p, Val.int n)}
  let f : Val := .fun .q <| .seq (.app incr p) (.app incr .q)
  fun
  | _, rfl => .app₁ (fun v h => v = f ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  let n' : Int := n + 1
  .app_fun <| .seq (fun _ => HProp.hsingle p n') (triple_incr _ _ _ rfl) fun
  | _, _, rfl =>
  let s' : Heap := {(p, Val.int n')}
  let n'' : Int := n' + 1
  have e : n + 2 = n'' := by lia
  suffices Eval (fun _ => HProp.hsingle p n'') (.app incr p) s' by rw [e]; exact this
  triple_incr p n' s' rfl

def aliased_call : Val :=
  .fun .p <| .app (.app incr_two .p) .p

theorem triple_aliased_call (p : Loc) (n : Int) :
  Triple (.app aliased_call p)
    (.hsingle p n)
    fun _ => .hsingle p (n + 2 : Int)
:=
  fun
  | _, rfl => .app_fun <| triple_incr_two_aliased _ _ _ rfl

def incr_first : Val :=
  .fun .p <| .fun .q <| .app incr .p

theorem triple_incr_first (p q : Loc) (m n : Int) :
  Triple (.app (.app incr_first p) q)
    (.hsingle p m * .hsingle q n)
    fun _ => .hsingle p (m + 1 : Int) * .hsingle q n
:=
  let f : Val := .fun .q <| .app incr p
  fun
  | _, ⟨s₁, s₂, h₁, h₂, h, rfl⟩ => .app₁ (fun v s => v = f ∧ s = s₁ ∪ s₂) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <| .frame₁ h h₂ <| triple_incr p m s₁ h₁

theorem triple_incr_first' (p q : Loc) (m : Int) :
  Triple (.app (.app incr_first p) q)
    (.hsingle p m)
    fun _ => .hsingle p (m + 1 : Int)
:=
  let s : Heap := {(p, Val.int m)}
  let f : Val := .fun .q <| .app incr p
  fun
  | _, rfl => .app₁ (fun v h => v = f ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <| triple_incr _ _ _ rfl

/-- `triple_incr_first_derived` -/
example (p q : Loc) (m n : Int) :
  Triple (.app (.app incr_first p) q)
    (.hsingle p m * .hsingle q n)
    fun _ => .hsingle p (m + 1 : Int) * .hsingle q n
:=
  fun
  | _, ⟨_, _, rfl, rfl, h, rfl⟩ => .frame₁ h rfl <| triple_incr_first' _ _ _ _ rfl

def transfer : Val :=
  .fun .p <| .fun .q <|
    .let .m (.get .p) <|
    .let .n (.get .q) <|
    .let .s (.m + .n) <|
 Trm.set .p .s |>.seq <|
    .set .q 0

theorem triple_transfer (p q : Loc) (m n : Int) :
  Triple (.app (.app transfer p) q)
    (.hsingle p m * .hsingle q n)
    fun _ => .hsingle p (m + n) * .hsingle q (0 : Int)
:=
  let k : Int := m + n
  let Q _ := HProp.hsingle p k * HProp.hsingle q (Val.int 0)
  let s₁ : Heap := {(p, Val.int m)}
  let s₂ : Heap := {(q, Val.int n)}
  let s : Heap := s₁ ∪ s₂
  fun
  | _, ⟨_, _, rfl, rfl, h, rfl⟩ => show Eval Q (.app (.app transfer p) q) s from
  let t := .let .m (.get p) <| .let .n (.get .q) <| .let .s (.m + .n) <| .seq (.set p .s) (.set .q 0)
  .app₁ (fun v h => v = Val.fun .q t ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => show Eval Q (.app (Val.fun .q t) q) s from
  let t := .let .m (.get p) <| .let .n (.get q) <| .let .s (.m + .n) <| .seq (.set p .s) (.set q 0)
  suffices Eval Q t s from .app_fun this
  .let (fun v h => v = m ∧ h = s) (.get (Heap.mem_union_of_left Heap.singleton_mem)
    ⟨Heap.union_get_left Heap.singleton_mem (h p Heap.singleton_mem) |>.trans Heap.singleton_get, rfl⟩
  ) fun
  | _, _, ⟨rfl, rfl⟩ =>
  show Eval Q (.let .n (.get q) <| .let .s (m + .n) <| .seq (.set p .s) (.set q 0)) s from
  .let (fun v h => v = n ∧ h = s) (.get (Heap.mem_union_of_right Heap.singleton_mem)
    ⟨Heap.union_get_right Heap.singleton_mem |>.trans Heap.singleton_get, rfl⟩
  ) fun
  | _, _, ⟨rfl, rfl⟩ =>
  show Eval Q (.let .s (m + n) <| .seq (.set p .s) (.set q 0)) s from
  .let (fun v h => v = k ∧ h = s) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  show Eval Q (.seq (.set p k) (.set q 0)) s from
  .seq (fun _ => HProp.hsingle p k * HProp.hsingle q n) (
    .frame₁ h rfl <| .set Heap.singleton_mem Heap.singleton_insert
  ) fun
  | _, _, ⟨_, _, rfl, rfl, h, rfl⟩ =>
  show Eval Q (.set q 0) ({(p, Val.int k)} ∪ s₂) from
  .frame₂ h rfl <| .set Heap.singleton_mem Heap.singleton_insert

theorem triple_transfer_aliased (p : Loc) (m : Int) :
  Triple (.app (.app transfer p) p)
    (.hsingle p m)
    fun _ => .hsingle p (0 : Int)
:=
  let s : Heap := {(p, Val.int m)}
  let f : Val := .fun .q <|
    .let .m (.get p) <|
    .let .n (.get .q) <|
    .let .s (.m + .n) <|
    .seq (.set p .s) (.set .q 0)
  fun
  | _, rfl => .app₁ (fun v h => v = f ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <|
  .let (fun v h => v = m ∧ h = s) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  .let (fun v h => v = m ∧ h = s) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = m + m ∧ h = s) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  .seq (fun _ => HProp.hsingle p (m + m)) (.set Heap.singleton_mem Heap.singleton_insert) fun
  | _, _, rfl => .set Heap.singleton_mem Heap.singleton_insert

/-- Originally, `triple_ref'`. -/
theorem triple_ref (v : Val) :
  Triple (.ref v)
    .hempty
    (.funloc fun p : Loc => .hsingle p v)
:=
  fun
  | _, rfl => .ref fun p _ =>
  let s : Heap := {(p, v)}
  ⟨p, ⟨∅, s, ⟨rfl, rfl⟩, rfl, s.empty_disjoint, s.empty_union⟩⟩

/-- Originally, `triple_ref`. -/
example (v : Val) :
  Triple (.ref v)
    .hempty
    fun r => .hexists fun p : Loc => .hpure (r = p) * .hsingle p v
:=
  triple_ref v

def ref_greater : Val :=
  .fun .p <|
    .let .n (.get .p) <|
    .let .m (.n + 1) <|
    .ref .m

theorem triple_ref_greater (p : Loc) (n : Int) :
  Triple (.app ref_greater p)
    (.hsingle p n)
    (.funloc fun q => .hsingle p n * .hsingle q (n + 1 : Int))
:=
  let s₁ : Heap := {(p, Val.int n)}
  let m : Int := n + 1
  fun
  | _, rfl => .app_fun <|
  .let (fun v h => v = n ∧ h = s₁) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = m ∧ h = s₁) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  let t : Trm := .ref m
  show Eval (HProp.funloc fun q => HProp.hsingle p n * HProp.hsingle q m) t s₁ from
  .ref fun q hq =>
  let s₂ : Heap := {(q, Val.int m)}
  let s : Heap := s₁ ∪ s₂
  have d : Disjoint s₁ s₂ := fun k m₁ m₂ =>
    suffices q ∈ s₁ from hq this
    suffices p = q from this.subst (Heap.singleton_mem : p ∈ s₁)
    calc p
     _ = k := Heap.eq_of_mem_singleton m₁
     _ = q := Heap.eq_of_mem_singleton m₂ |>.symm
  suffices _ from ⟨q, ∅, s, ⟨rfl, rfl⟩, ⟨s₁, s₂, rfl, rfl, d, rfl⟩, s.empty_disjoint, this⟩
  calc s₁.insert q m
   _ = s₁ ∪ s₂ := s₁.union_singleton_of_insert
   _ = ∅ ∪ s := s.empty_union

theorem triple_ref_frame₂ H {v : Val} : Triple (.ref v) H (.funloc fun p => H * .hsingle p v)
  | s₁, h₁ => .ref fun q hq =>
    let s : Heap := s₁.insert q v
    let s₂ : Heap := {(q, v)}
    show HProp.funloc (H * HProp.hsingle · v) q s from
    suffices H * HProp.funloc (HProp.hsingle · v) q <| s from HProp.hstar_funloc.rec this
    let h₂ := ⟨q, ∅, s₂, ⟨rfl, rfl⟩, rfl, s₂.empty_disjoint, rfl⟩
    suffices Disjoint s₁ s₂ from ⟨s₁, s₂, h₁, h₂, this, s₁.union_singleton_of_insert⟩
    fun p m₁ m₂ =>
      suffices q ∈ s₁ from hq this
      suffices q = p from this.symm.subst m₁
      Heap.eq_of_mem_singleton m₂

theorem triple_ref_frame₁ H {v : Val} : Triple (.ref v) H (.funloc fun p => .hsingle p v * H) :=
  by (conv => arg 3; arg 1; ext; rw [HProp.hstar.comm]); exact triple_ref_frame₂ H

example (p : Loc) (n : Int) : type_of% (triple_ref_greater p n) :=
  let s₁ : Heap := {(p, Val.int n)}
  let m : Int := n + 1
  fun
  | _, rfl => .app_fun <|
  .let (fun v h => v = n ∧ h = s₁) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = m ∧ h = s₁) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  show Eval (HProp.funloc fun q => HProp.hsingle p n * HProp.hsingle q m) (.ref m) s₁ from
  triple_ref_frame₂ _ _ rfl

theorem triple_ref_greater_abstract (p : Loc) (n : Int) :
  Triple (.app ref_greater p)
    (.hsingle p n)
    (.funloc fun q => .hsingle p n * .hexists fun m : Int => .hpure (m > n) * .hsingle q m)
:=
  let s₁ : Heap := {(p, Val.int n)}
  fun
  | _, rfl => (triple_ref_greater p n s₁ rfl).conseq fun
  | _, _, ⟨q, _, _, ⟨rfl, rfl⟩, ⟨_, _, rfl, rfl, d, rfl⟩, d', rfl⟩ =>
  let m : Int := n + 1
  let s₂ : Heap := {(q, Val.int m)}
  have := s₂.empty_disjoint
  ⟨q, ∅, _, ⟨rfl, rfl⟩, ⟨s₁, s₂, rfl, ⟨m, ∅, s₂, ⟨n.lt_succ, rfl⟩, rfl, this, rfl⟩, d, rfl⟩, d', rfl⟩

theorem triple_ref_with_frame (p' : Loc) (v' v : Val) :
  Triple (.ref v)
    (.hsingle p' v')
    (.funloc fun p => .hsingle p v * .hsingle p' v')
:=
  triple_ref_frame₁ _

def succ_using_incr_attempt : Val :=
  .fun .n <|
    .let .p (.ref .n) <|
 Trm.app incr .p |>.seq <|
    .get .p

theorem triple_succ_using_incr_attempt' (n : Int) :
  Triple (.app succ_using_incr_attempt n)
    .hempty
    fun r => .hpure (r = (n + 1 : Int)) * .hexists fun p => .hsingle p (n + 1 : Int)
:=
  let m : Int := n + 1
  fun
  | _, rfl => .app_fun <| .let (HProp.funloc (HProp.hsingle · n)) (triple_ref n ∅ rfl) fun
  | _, _, ⟨p, _, _, ⟨rfl, rfl⟩, rfl, _, rfl⟩ => .seq (fun _ => HProp.hsingle p m) (triple_incr p n _ rfl) fun
  | _, _, rfl =>
  let s : Heap := {(p, Val.int m)}
  .get Heap.singleton_mem ⟨∅, s, ⟨Heap.singleton_get, rfl⟩, ⟨p, rfl⟩, s.empty_disjoint, s.empty_union⟩

theorem triple_succ_using_incr_attempt (n : Int) :
  ¬Triple (.app succ_using_incr_attempt n)
    .hempty
    fun r => .hpure (r = (n + 1 : Int))
:=
  fun h =>
  match (h ∅ rfl).and_eventually (triple_succ_using_incr_attempt' n ∅ rfl) with
  | ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, ⟨p, rfl⟩, _, e⟩ =>
  have : p ∈ ∅ ∪ {(p, Val.int (n + 1))} := Heap.singleton_mem
  Heap.not_mem_empty <| e.symm ▸ this

def succ_using_incr : Val :=
  .fun .n <|
    .let .p (.ref .n) <|
 Trm.app incr .p |>.seq <|
    .let .x (.get .p) <|
 Trm.free .p |>.seq <|
    .x

section

variable {p : Loc} {v w : Val}
theorem triple_get : Triple (.get p) (.hsingle p v) fun r h => r = v ∧ HProp.hsingle p v h
  | _, rfl => .get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩
theorem triple_set : Triple (.set p w) (.hsingle p v) fun _ => .hsingle p w
  | _, rfl => .set Heap.singleton_mem Heap.singleton_insert
theorem triple_free : Triple (.free p) (.hsingle p v) fun _ => .hempty
  | _, rfl => .free Heap.singleton_mem Heap.singleton_erase

end

theorem triple_succ_using_incr (n : Int) :
  Triple (.app succ_using_incr n)
    .hempty
    fun r => .hpure (r = (n + 1 : Int))
:=
  fun
  | _, rfl => .app_fun <| .let _ (triple_ref n ∅ rfl) fun
  | _, _, ⟨p, _, _, ⟨rfl, rfl⟩, rfl, _, rfl⟩ => .seq _ (triple_incr p n _ rfl) fun
  | _, _, rfl => .let _ (triple_get _ rfl) fun
  | _, _, ⟨rfl, rfl⟩ => .seq _ (triple_free _ rfl) fun
  | _, _, rfl => .val ⟨rfl, rfl⟩

def get_and_free : Val :=
  .fun .p <|
    .let .v (.get .p) <|
 Trm.free .p |>.seq <|
    .v

theorem triple_get_and_free (p : Loc) (v : Val) :
  Triple (.app get_and_free p)
    (.hsingle p v)
    fun r => .hpure (r = v)
:=
  fun
  | _, rfl => .app_fun <| .let _ (triple_get _ rfl) fun
  | _, _, ⟨rfl, rfl⟩ => .seq _ (triple_free _ rfl) fun
  | _, _, rfl => .val ⟨rfl, rfl⟩

theorem triple_rand (n : Int) (hn : n > 0) :
  Triple (.rand n)
    .hempty
    <| .funint fun m => .hpure (0 ≤ m ∧ m < n)
:=
  fun
  | _, rfl => .rand hn fun m hge hlt => ⟨m, ∅, ∅, ⟨rfl, rfl⟩, ⟨⟨hge, hlt⟩, rfl⟩, Heap.empty_disjoint, rfl⟩

def two_dice : Val :=
  .fun .v <|
    .let .m (.rand 6) <|
    .let .n (.rand 6) <|
    .let .s (.m + .n) <|
    .s + 2

theorem triple_two_dice :
  Triple (.app two_dice ())
    .hempty
    <| .funint fun m => .hpure (2 ≤ m ∧ m ≤ 12)
:=
  have h6 : (6 : Int) > 0 := ⟨5⟩
  fun
  | _, rfl => .app_fun <| .let _ (triple_rand 6 h6 ∅ rfl) fun
  | _, _, ⟨m, _, _, ⟨rfl, rfl⟩, ⟨hm, rfl⟩, _, rfl⟩ => .let _ (triple_rand 6 h6 ∅ rfl) fun
  | _, _, ⟨n, _, _, ⟨rfl, rfl⟩, ⟨hn, rfl⟩, _, rfl⟩ =>
  .let (fun v h => v = m + n ∧ h = ∅) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .add ⟨m + n + 2, ∅, ∅, ⟨rfl, rfl⟩, ⟨by lia, rfl⟩, Heap.empty_disjoint, rfl⟩

namespace Facto

axiom facto : Int → Int
variable {n : Int}
/-- Originally, `axiom facto_init (h : 0 ≤ n ∧ n ≤ 1) : facto n = 1`. -/
axiom facto_zero : facto 0 = 1
axiom facto_step (h : 1 ≤ n) : facto n = n * facto (n - 1)

theorem facto_one : facto 1 = 1 :=
  calc facto 1
   _ = 1 * facto 0 := facto_step ⟨0⟩
   _ = 1 * 1 := congrArg _ facto_zero
   _ = 1 := rfl
theorem facto_two : facto 2 = 2 :=
  calc facto 2
   _ = 2 * facto 1 := facto_step ⟨1⟩
   _ = 2 * 1 := congrArg _ facto_one
   _ = 2 := rfl
theorem facto_three : facto 3 = 6 :=
  by simp [facto_step, facto_zero]
theorem facto_succ (h : 0 ≤ n) : facto (n + 1) = (n + 1) * facto n :=
  calc facto (n + 1)
   _ = (n + 1) * facto (n + 1 - 1) := facto_step (Int.add_le_add_right h 1)
   _ = (n + 1) * facto n := n.add_sub_cancel 1 |>.symm.rec rfl

end Facto

def factorec : Val :=
  .fix .f .n <|
    .let .b (.le .n 1) <|
    .if .b 1 <|
      .let .x (.n - 1) <|
      .let .y (.app .f .x) <|
      .n * .y

open Facto in
theorem triple_factorec (n : Int) (h : n ≥ 0) :
  Triple (.app factorec n)
    .hempty
    fun r => .hpure (r = facto n)
:=
  fun
  | _, rfl => .app_fix <|
  match n with
  | Int.negSucc _ => nomatch h
  | 0 => .let (fun v s => v = true ∧ s = ∅) (.le ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ =>
    suffices Eval (fun r => HProp.hpure (r = facto 0)) 1 ∅ from .if this
    .val ⟨congrArg Val.int facto_zero.symm, rfl⟩
  | 1 => .let (fun v s => v = true ∧ s = ∅) (.le ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ =>
    suffices Eval (fun r => HProp.hpure (r = facto 1)) 1 ∅ from .if this
    .val ⟨congrArg Val.int facto_one.symm, rfl⟩
  | Int.ofNat (n + 2) => .let (fun v s => v = false ∧ s = ∅) (.le ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ =>
    let m : Int := n + 2
    let x : Int := n + 1
    let t : Trm :=
        .let Var.x (m - 1) <|
        .let Var.y (.app factorec Var.x) <|
        m * Var.y
    suffices Eval (fun r => HProp.hpure (r = facto m)) t ∅ from .if this
    .let (fun v s => v = x ∧ s = ∅) (.sub ⟨congrArg Val.int (x.add_sub_cancel 1), rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ =>
    have hx : x ≥ 0 := ⟨n + 1⟩
    .let (fun r => HProp.hpure (r = facto x)) (triple_factorec x hx ∅ rfl) fun
    | _, _, ⟨rfl, rfl⟩ =>
    .mul ⟨congrArg Val.int (facto_succ hx).symm, rfl⟩
termination_by n.toNat

def repeat_incr : Val :=
  .fix .f .p <| .fun .n <|
    .let .b (.gt .n 0) <|
    .if .b (
   Trm.app incr .p |>.seq <|
      .let .x (.n - 1) <|
      .app (.app .f .p) .x
    ) ()

/-- Originally, `triple_repeat_incr'`. -/
theorem triple_repeat_incr (p : Loc) (m n : Int) (h : n ≥ 0) :
  Triple (.app (.app repeat_incr p) n)
    (.hsingle p m)
    fun _ => .hsingle p (m + n)
:=
  let s : Heap := {(p, Val.int m)}
  let g : Val :=
    .fun .n <|
      .let .b (.gt .n 0) <|
      .if .b (
        .seq (.app incr p) <|
        .let .x (.n - 1) <|
        .app (.app repeat_incr p) .x
      ) ()
  fun
  | _, rfl => .app₁ (fun v h => v = g ∧ h = s) id (.app_fix <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <|
  match n, h with
  | 0, _ => .let (fun v h => v = false ∧ h = s) (.gt ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <| .val <| m.add_zero.symm.rec rfl
  | (n + 1 : Nat), h => .let (fun v h => v = true ∧ h = s) (.gt ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <| .seq _ (triple_incr p m s rfl) fun
    | _, _, rfl =>
    let s : Heap := {(p, Val.int (m + 1))}
    let n : Int := n
    .let (fun v h => v = n ∧ h = s) (.sub ⟨congrArg Val.int (n.add_sub_cancel 1), rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ =>
    show Eval (fun _ => HProp.hsingle p (m + (n + 1))) (.app (.app repeat_incr p) n) s from
    have : m + 1 + n = m + (n + 1) := by ac_nf
    this.rec <| triple_repeat_incr p (m + 1) n ⟨n.toNat⟩ s rfl
termination_by n.toNat

/-- Originally, `triple_repeat_incr`. -/
example (m n : Int) (p : Loc) (h : m ≥ 0) :
  Triple (.app (.app repeat_incr p) m)
    (.hsingle p n)
    fun _ => .hsingle p (n + m)
:=
  triple_repeat_incr p n m h

/-- Originally, `triple_repeat_incr_incorrect`. -/
example (p : Loc) (m : Int) : ¬∀ n : Int,
  Triple (.app (.app repeat_incr p) n)
    (.hsingle p m)
    fun _ => .hsingle p (m + n)
:=
  fun h =>
  let s : Heap := {(p, Val.int m)}
  let t : Trm := .app (.app repeat_incr p) (-1 : Int)
  have e : Eval (fun _ => .hsingle p (m - 1 : Int)) t s := h (-1) s rfl
  have e' : Eval (fun _ => .hsingle p m) t s :=
    let g : Val := .fun .n <| .let .b (.gt .n 0) <| .if .b _ ()
    .app₁ (fun v h => v = g ∧ h = s) id (.app_fix <| .fun ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .app_fun <| .let (fun v h => v = false ∧ h = s) (.gt ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <| .val rfl
  match e.and_eventually e' with
  | ⟨_, _, rfl, e⟩ => Int.ne_of_lt (m.sub_lt_self ⟨0⟩) <| Val.int.inj <| Heap.singleton_inj e

/-- Originally, `max_l`. -/
example (m n : Int) : m ≥ n → max m n = m := Int.max_eq_left

/-- Originally, `max_r`. -/
example (m n : Int) : m ≤ n → max m n = n := Int.max_eq_right

theorem triple_repeat_incr' (p : Loc) (m n : Int) :
  Triple (.app (.app repeat_incr p) n)
    (.hsingle p m)
    fun _ => .hsingle p (m + max 0 n)
:=
  match n with
  | Int.ofNat n => triple_repeat_incr p m (Int.ofNat n) ⟨n⟩
  | Int.negSucc _ =>
    let s : Heap := {(p, Val.int m)}
    let g : Val := .fun .n <| .let .b (.gt .n 0) <| .if .b _ ()
    fun
    | _, rfl => .app₁ (fun v h => v = g ∧ h = s) id (.app_fix <| .fun ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .app_fun <| .let (fun v h => v = false ∧ h = s) (.gt ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <| .val <| m.add_zero.symm.rec rfl

def decr : Val :=
  .fun .p <|
    .let .n (.get .p) <|
    .let .m (.n - 1) <|
    .set .p .m

theorem triple_decr (p : Loc) (n : Int) :
  Triple (.app decr p)
    (.hsingle p n)
    fun _ => .hsingle p (n - 1 : Int)
:=
  let s : Heap := {(p, Val.int n)}
  fun
  | _, rfl => .app_fun <|
  .let (fun v h => v = n ∧ h = s) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = (n - 1 : Int) ∧ h = s) (.sub ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .set Heap.singleton_mem Heap.singleton_insert

def step_transfer : Val :=
  .fix .f .p <| .fun .q <|
    .let .n (.get .q) <|
    .let .b (.gt .n 0) <|
    .if .b (
   Trm.app incr .p |>.seq <|
   Trm.app decr .q |>.seq <|
      .app (.app .f .p) .q
    ) ()

theorem triple_step_transfer (p q : Loc) (m n : Int) (hn : n ≥ 0) :
  Triple (.app (.app step_transfer p) q)
    (.hsingle p m * .hsingle q n)
    fun _ => .hsingle p (m + n) * .hsingle q (0 : Int)
:=
  let s : Heap := {(p, Val.int m)} ∪ {(q, Val.int n)}
  let g : Val :=
    .fun .q <|
      .let .n (.get .q) <|
      .let .b (.gt .n 0) <|
      .if .b (
        .seq (.app incr p) <|
        .seq (.app decr .q) <|
              .app (.app step_transfer p) .q
      ) ()
  fun
  | _, ⟨_, _, rfl, rfl, h, rfl⟩ => .app₁ (fun v h => v = g ∧ h = s) id (.app_fix <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <| .let (fun v h => v = n ∧ h = s) (
    .get (Heap.mem_union_of_right Heap.singleton_mem)
      ⟨Heap.union_get_right Heap.singleton_mem |>.trans Heap.singleton_get, rfl⟩
  ) fun
  | _, _, ⟨rfl, rfl⟩ =>
  match e : n with
  | 0 =>
    .let (fun v h => v = false ∧ h = s) (.gt ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <| .val <|
    suffices HProp.hsingle p m * HProp.hsingle q (0 : Int) <| _ from m.add_zero.symm.rec this
    ⟨_, _, rfl, rfl, h, e.rec rfl⟩
  | (k + 1 : Nat) => .let (fun v h => v = true ∧ h = s) (.gt ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <| .seq _ (.frame₁ h rfl <| triple_incr _ _ _ rfl) fun
    | _, _, ⟨_, _, rfl, rfl, _, rfl⟩ => .seq _ (.frame₂ h rfl <| triple_decr _ _ _ rfl) fun
    | _, _, ⟨_, _, rfl, rfl, _, rfl⟩ =>
    let t : Trm := .app (.app step_transfer p) q
    let H₂ : HProp := HProp.hsingle q (0 : Int)
    let s₁ : Heap := {(p, Val.int (m + 1))}
    show Eval (fun _ => HProp.hsingle p (m + (k + 1 : Int)) * H₂) t <| s₁ ∪ {(q, Val.int (n - 1))} from
    suffices Eval (fun _ => HProp.hsingle p (m + 1 + k : Int) * H₂) t <| s₁ ∪ {(q, Val.int k)} by
      have e₁ : m + (k + 1) = m + 1 + k := by ac_rfl
      have e₂ : n - 1 = k := by lia
      rw [e₁, e₂]; exact this
    triple_step_transfer p q (m + 1) k ⟨k⟩ _ ⟨_, _, rfl, rfl, h, rfl⟩
termination_by n.toNat

def factoimp_aux : Val :=
  .fix .f .r <| .fun .i <| .fun .n <|
    .let .b (.lt .i .n) <|
    .if .b (
      .let .j (.i + 1) <|
      .let .s (.get .r) <|
      .let .p (.s * .j) <|
   Trm.set .r .p |>.seq <|
      .app (.app (.app .f .r) .j) .n
    ) ()

def factoimp : Val :=
  .fun .n <|
    .let .r (.ref 1) <|
 Trm.app (.app (.app factoimp_aux .r) 1) .n |>.seq <|
    .let .m (.get .r) <|
 Trm.free .r |>.seq <|
    .m

open Facto in
theorem triple_factoimp_aux (r : Loc) (i n : Int) (hge : 0 ≤ i) (hle : i ≤ n) :
  Triple (.app (.app (.app factoimp_aux r) i) n)
    (.hsingle r (facto i))
    fun _ => .hsingle r (facto n)
:=
  let s : Heap := {(r, Val.int (facto i))}
  let t : Trm :=
    .let .s (.get r) <|
    .let .p (.s * .j) <|
    .seq (.set r .p) <|
    .app (.app (.app factoimp_aux r) .j) .n
  let g : Val :=
    .fun .n <|
      .let .b (.lt i .n) <|
      .if .b (
        .let .j (i + 1) <|
        t
      ) ()
  fun
  | _, rfl => .app₁ (fun v h => v = g ∧ h = s) id (
    let g : Val :=
      .fun .i <| .fun .n <|
        .let .b (.lt .i .n) <|
        .if .b (
          .let .j (.i + 1) <|
          t
        ) ()
    .app₁ (fun v h => v = g ∧ h = s) id (.app_fix <| .fun ⟨rfl, rfl⟩) fun
    | _ , _, ⟨rfl, rfl⟩ => .app_fun <| .fun ⟨rfl, rfl⟩
  ) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <|
  if h : i < n then
    .let (fun v h => v = true ∧ h = s) (.lt ⟨by simp [h], rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <|
    let j : Int := i + 1
    .let (fun v h => v = j ∧ h = s) (.add ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = facto i ∧ h = s) (triple_get _ rfl) fun
    | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = facto i * j ∧ h = s) (.mul ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .seq (fun _ => HProp.hsingle r (facto i * j)) (triple_set _ rfl) fun
    | _, _, rfl =>
    have e :=
      calc facto j
       _ = j * facto i := facto_succ hge
       _ = facto i * j := Int.mul_comm ..
    triple_factoimp_aux _ _ _ (Int.le_add_one hge) h _ (e.rec rfl)
  else
    .let (fun v h => v = false ∧ h = s) (.lt ⟨by simp [h], rfl⟩) fun
    | _, _, ⟨rfl ,rfl⟩ => .if <| .val <| suffices i = n from this.rec rfl
    Int.le_antisymm hle (Int.le_of_not_gt h)
termination_by (n - i).toNat

open Facto in
theorem triple_factoimp (n : Int) (hn : n ≥ 1) :
  Triple (.app factoimp n)
    .hempty
    fun r => .hpure (r = facto n)
:=
  let i := Val.int 1
  fun
  | _, rfl => .app_fun <| .let _ (triple_ref i ∅ rfl) fun
  | _, _, ⟨r, _, _, ⟨rfl, rfl⟩, rfl, _, rfl⟩ =>
  let s : Heap := {(r, i)}
  have : HProp.hsingle r (facto 1) (∅ ∪ s) :=
    calc ∅ ∪ s
     _ = s := s.empty_union
     _ = {(r, Val.int (facto 1))} := facto_one.symm.rec rfl
  .seq (fun _ => HProp.hsingle r (facto n)) (triple_factoimp_aux r 1 n ⟨1⟩ hn _ this) fun
  | _, _, rfl => .let _ (triple_get _ rfl) fun
  | _, _, ⟨rfl, rfl⟩ => .seq _ (triple_free _ rfl) fun
  | _, _, rfl => .val ⟨rfl, rfl⟩

end Basic
