import SoftwareFoundations.SLF.StdExtra
set_option linter.constructorNameAsVariable false
/-
Does not cover CFML which applies separation logic to reasoning about OCaml programs.
Prerequisites: volume 1, Hoare and Hoare2 from volume 2.
-/

section LibSepReference

abbrev Loc := Nat

inductive Var
  | a | b | f | m | n | p | q | s | x | y
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
  | add : Trm → Trm → Trm
  | sub : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  | eq  : Trm → Trm → Trm
  | ne  : Trm → Trm → Trm
  | le  : Trm → Trm → Trm
  | lt  : Trm → Trm → Trm
  | ge  : Trm → Trm → Trm
  | gt  : Trm → Trm → Trm
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
)

variable {p : Loc} {v w : Val}
theorem singleton_mem : p ∈ ({(p, v)} : Heap) :=
  Std.ExtTreeMap.mem_insert_self
theorem singleton_get : ({(p, v)} : Heap).get p singleton_mem = v :=
  Std.ExtTreeMap.getElem_insert_self
theorem singleton_insert : ({(p, v)} : Heap).insert p w = {(p, w)} :=
  Std.ExtTreeMap.ext_getElem? fun k =>
  let s : Heap := ∅
  let t : Heap := {(p, v)}
  calc (t.insert p w)[k]?
   _ = if _ then some w else t[k]? := Std.ExtTreeMap.getElem?_insert
   _ = if _ then some w else s[k]? := ite_congr rfl (fun _ => rfl) fun hn =>
    calc t[k]?
     _ = if _ then some v else s[k]? := Std.ExtTreeMap.getElem?_insert
     _ = s[k]? := ite_eq_right hn
   _ = {(p, w)}[k]? := Std.ExtTreeMap.getElem?_insert.symm
theorem singleton_inj (h : @Eq Heap {(p, v)} {(p, w)}) : v = w :=
  Option.some.inj <|
    calc some v
    _ = ({(p, v)} : Heap)[p]? := Std.ExtTreeMap.getElem?_insert_self.symm
    _ = ({(p, w)} : Heap)[p]? := h ▸ rfl
    _ = some w := Std.ExtTreeMap.getElem?_insert_self

variable {s₁ s₂ : Heap}
theorem union_get_left_of_disjoint (h : Disjoint s₁ s₂) (m : p ∈ s₁) :
    (s₁ ∪ s₂).get p (mem_union_of_left m) = s₁.get p m :=
  Option.some.inj <|
    calc some ((s₁ ∪ s₂).get p (mem_union_of_left m))
    _ = (s₁ ∪ s₂)[p]? := Std.ExtTreeMap.getElem?_eq_some_getElem _ |>.symm
    _ = s₁[p]? := Std.ExtTreeMap.getElem?_union_of_not_mem_right (h p m)
    _ = some (s₁.get p m) := Std.ExtTreeMap.getElem?_eq_some_getElem _
theorem insert_left_of_disjoint (h : Disjoint s₁ s₂) (m : p ∈ s₁) :
    Disjoint (s₁.insert p v) s₂
  | q, (m₁ : q ∈ s₁.insert p v), (m₂ : q ∈ s₂) =>
    match Std.ExtTreeMap.mem_insert.mp m₁ with
    | .inl e => h p m <| Std.LawfulEqCmp.eq_of_compare e |>.symm.subst m₂
    | .inr m₁ => h q m₁ m₂
theorem union_insert_left_of_disjoint (h : Disjoint s₁ s₂) (m : p ∈ s₁) :
    (s₁ ∪ s₂).insert p v = s₁.insert p v ∪ s₂ :=
  calc (s₁ ∪ s₂).insert p v
   _ = (s₂ ∪ s₁).insert p v := congrArg (·.insert p v) <| union_comm_of_disjoint h
   _ = s₂ ∪ s₁.insert p v := Std.ExtTreeMap.union_insert_right_eq_insert_union (p := ⟨p, v⟩) |>.symm
   _ = s₁.insert p v ∪ s₂ := union_comm_of_disjoint (insert_left_of_disjoint h m).symm

theorem empty_disjoint : Disjoint ∅ s₂
  | _, m₁, _ => nomatch m₁
theorem empty_union : s₂ = ∅ ∪ s₂ :=
  Std.ExtTreeMap.empty_union.symm
theorem union_get_right (m : p ∈ s₂) : (s₁ ∪ s₂).get p (mem_union_of_right m) = s₂.get p m :=
  Std.ExtTreeMap.getElem_union_of_mem_right m

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
def htop : HProp := hexists fun H : HProp => H
def hwand (H₁ H₂ : HProp) : HProp := hexists fun H₀ => H₀ * (hpure <| (H₁ * H₀).himpl H₂)
def qwand (Q₁ Q₂ : α → HProp) : HProp := hforall fun x => (Q₁ x).hwand (Q₂ x)

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
  fun | _, ⟨_, h, rfl, p, _, rfl⟩ => h.empty_union.subst p
  fun | h, p => ⟨_, h, rfl, p, (fun _ m _ => nomatch m), h.empty_union⟩
theorem hstar_hempty : H * hempty = H :=
  hstar.comm.trans hempty_hstar

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
  | get src => get src.subst
  | set dst src => set dst.subst src.subst
  | add lhs rhs => add lhs.subst rhs.subst
  | sub lhs rhs => sub lhs.subst rhs.subst
  | mul lhs rhs => mul lhs.subst rhs.subst
  | eq  lhs rhs => eq  lhs.subst rhs.subst
  | ne  lhs rhs => ne  lhs.subst rhs.subst
  | le  lhs rhs => le  lhs.subst rhs.subst
  | lt  lhs rhs => lt  lhs.subst rhs.subst
  | ge  lhs rhs => ge  lhs.subst rhs.subst
  | gt  lhs rhs => gt  lhs.subst rhs.subst

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
  | .if       e₁   => .if       (e₁.frame₁ q h₂)
  | app_fun   e₁   => app_fun   (e₁.frame₁ q h₂)
  | app_fix   e₁   => app_fix   (e₁.frame₁ q h₂)
  | app₁ _ hn e₁ h => app₁ _ hn (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | app₂ _ hn e₁ h => app₂ _ hn (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | .let _    e₁ h => .let _    (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | seq  _    e₁ h => seq  _    (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
  | get m₁ h₁ => get (Heap.mem_union_of_left m₁) ⟨s₁, s₂, Heap.union_get_left_of_disjoint q m₁ ▸ h₁, h₂, q, rfl⟩
  | set m₁ h₁ => set (Heap.mem_union_of_left m₁) ⟨_, s₂, h₁, h₂, Heap.insert_left_of_disjoint q m₁,
    Heap.union_insert_left_of_disjoint q m₁⟩
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
  |  set _     h => ⟨_, _, h⟩
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

end Eval

def Triple (t : Trm) (H : HProp) (Q : Val → HProp) := ∀ s, H s → Eval Q t s

end LibSepReference

namespace Trm

instance {n} : OfNat Trm n where ofNat := Val.int n
instance : Add Trm where add := add
instance : Sub Trm where sub := sub
instance : Mul Trm where mul := mul

export Var (a b f m n p q s x y)

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
  | _, _, ⟨rfl, rfl⟩ => .set Heap.singleton_mem <| (show m = 2 * n by lia) ▸ Heap.singleton_insert

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
    ⟨Heap.union_get_left_of_disjoint h Heap.singleton_mem |>.trans Heap.singleton_get, rfl⟩
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

namespace Facto

axiom facto : Int → Int
variable {n : Int}
-- axiom facto_init (h : 0 ≤ n ∧ n ≤ 1) : facto n = 1
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
   _ = (n + 1) * facto n := n.add_sub_cancel 1 |>.symm ▸ rfl

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
    | _, _, ⟨rfl, rfl⟩ => .if <| .val <| m.add_zero.symm ▸ rfl
  | (n + 1 : Nat), h => .let (fun v h => v = true ∧ h = s) (.gt ⟨rfl, rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ => .if <| .seq _ (triple_incr p m s rfl) fun
    | _, _, rfl =>
    let s : Heap := {(p, Val.int (m + 1))}
    let n : Int := n
    .let (fun v h => v = n ∧ h = s) (.sub ⟨congrArg Val.int (n.add_sub_cancel 1), rfl⟩) fun
    | _, _, ⟨rfl, rfl⟩ =>
    show Eval (fun _ => HProp.hsingle p (m + (n + 1))) (.app (.app repeat_incr p) n) s from
    have : m + 1 + n = m + (n + 1) := by ac_nf
    this ▸ triple_repeat_incr p (m + 1) n ⟨n.toNat⟩ s rfl
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
    | _, _, ⟨rfl, rfl⟩ => .if <| .val <| m.add_zero.symm ▸ rfl

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
    suffices HProp.hsingle p m * HProp.hsingle q (0 : Int) <| _ from m.add_zero.symm ▸ this
    ⟨_, _, rfl, rfl, h, e ▸ rfl⟩
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

end Basic
