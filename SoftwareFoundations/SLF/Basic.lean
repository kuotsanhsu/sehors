import SoftwareFoundations.SLF.StdExtra
/-
Does not cover CFML which applies separation logic to reasoning about OCaml programs.
Prerequisites: volume 1, Hoare and Hoare2 from volume 2.
-/

section LibSepReference

abbrev Loc := Nat

inductive Var
  | a | b | m | n | p | q | s
deriving DecidableEq

mutual
inductive Val
  | unit
  | int : Int → Val
  | loc : Loc → Val
  | fun : Var → Trm → Val

inductive Trm
  | val : Val → Trm
  | var : Var → Trm
  | fun : Var → Trm → Trm
  | app : Trm → Trm → Trm
  | seq : Trm → Trm → Trm
  | let : Var → Trm → Trm → Trm
  -- Prim
  | get (p : Trm) : Trm
  | set (p v : Trm) : Trm
  | add : Trm → Trm → Trm
  | sub : Trm → Trm → Trm
end

instance : Coe Unit Val where coe _ := .unit
instance : Coe Int Val where coe := .int
instance : Coe Loc Val where coe := .loc
instance : Coe Val Trm where coe := .val
instance : Coe Var Trm where coe := .var

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
  | app fn arg => app fn.subst arg.subst
  | .let x rhs scope => .let x rhs.subst <| if x = y then scope else scope.subst
  | seq fst snd => seq fst.subst snd.subst
  -- Prim
  | get src => get src.subst
  | set dst src => set dst.subst src.subst
  | add lhs rhs => add lhs.subst rhs.subst
  | sub lhs rhs => sub lhs.subst rhs.subst

end Trm

/-!
## Omni-Big-Step Semantics
-/

inductive Eval : (Val → HProp) → Trm → HProp
  | val      {     s Q}   {v : Val} :        Q  v             s  → Eval Q  v                     s
  | add      {     s Q} {m n : Int} :        Q (m + n)        s  → Eval Q (.add m n)             s
  | sub      {     s Q} {m n : Int} :        Q (m - n)        s  → Eval Q (.sub m n)             s
  | fun      {t    s Q x}           :        Q (.fun   x   t) s  → Eval Q (.fun x t)             s
  | app_fun  {t    s Q x} {v : Val} :   Eval Q (.subst x v t) s  → Eval Q (.app (Val.fun x t) v) s
  | app₁ Q'  {t t' s Q} (hn : ¬t'.IsVal) :
    Eval Q'     t' s → (∀ v s, Q' v s → Eval Q (.app     v t) s) → Eval Q (t'.app   t)           s
  | let  Q'  {t t' s Q x} :
    Eval Q'     t' s → (∀ v s, Q' v s → Eval Q (.subst x v t) s) → Eval Q (t'.let x t)           s
  | seq  Q'  {t t' s Q} :
    Eval Q'     t' s → (∀ v s, Q' v s → Eval Q             t  s) → Eval Q (t'.seq   t)           s
  | get {p : Loc} {s Q} (m : p ∈ s) :        Q (s.get p m)    s  → Eval Q (.get p)               s
  | set {p : Loc} {s Q} (m : p ∈ s) {v : Val} : Q () (s.insert p v) → Eval Q (.set p v)          s

namespace Eval

theorem frame₁ {s₁ s₂ t Q H₂} (q : Disjoint s₁ s₂) (h₂ : H₂ s₂) : Eval Q t s₁ → Eval (fun v => Q v * H₂) t (s₁ ∪ s₂)
  |  val h₁ =>  val ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |  add h₁ =>  add ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  |  sub h₁ =>  sub ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  | .fun h₁ => .fun ⟨s₁, s₂, h₁, h₂, q, rfl⟩
  | app_fun   e₁   => app_fun   (e₁.frame₁ q h₂)
  | app₁ _ hn e₁ h => app₁ _ hn (e₁.frame₁ q h₂) fun | v, _, ⟨s₁, _, h₁, h₂, q, rfl⟩ => (h v s₁ h₁).frame₁ q h₂
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

end Eval

def Triple (t : Trm) (H : HProp) (Q : Val → HProp) := ∀ s, H s → Eval Q t s

end LibSepReference

namespace Trm

instance {n} : OfNat Trm n where ofNat := Val.int n
instance : Add Trm where add := add
instance : Sub Trm where sub := sub

export Var (a b m n p q s)

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
  let s := {(p, .int n)}
  let m := n + 1
  let Q _ := .hsingle p m
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
  let m := n + n
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
  let s := {(p, .int n)}
  let m := n + n
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
  let Q _ := .hsingle p x * .hsingle q y
  let f : Val := .fun .q <| .seq (.app incr p) (.app incr .q)
  fun
  | _, ⟨s₁, s₂, h₁, h₂, h, rfl⟩ => show Eval Q (.app (.app incr_two p) q) (s₁ ∪ s₂) from
  .app₁ (fun v s => v = f ∧ s = s₁ ∪ s₂) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => show Eval Q (.app f q) (s₁ ∪ s₂) from
  .app_fun <| .seq (fun _ => .hsingle p x * .hsingle q n) (.frame₁ h h₂ <| triple_incr p m s₁ h₁) fun
  | _, _, ⟨s₁, s₂, h₁, h₂, h, rfl⟩ => show Eval Q (.app incr q) (s₁ ∪ s₂) from
  .frame₂ h h₁ <| triple_incr q n s₂ h₂

theorem triple_incr_two_aliased (p : Loc) (n : Int) :
  Triple (.app (.app incr_two p) p)
    (.hsingle p n)
    fun _ => .hsingle p (n + 2 : Int)
:=
  let s : Heap := {(p, .int n)}
  let f : Val := .fun .q <| .seq (.app incr p) (.app incr .q)
  fun
  | _, rfl => .app₁ (fun v h => v = f ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <| .seq (fun _ => .hsingle p (n + 1 : Int)) (
    triple_incr _ _ _ <| show s = {(p, .int n)} from rfl
  ) fun
  | _, _, rfl =>
  let n' : Int := n + 1
  let s' : Heap := {(p, .int n')}
  let n'' : Int := n' + 1
  have e : n + 2 = n'' := by lia
  suffices Eval (fun _ => .hsingle p n'') (.app incr p) s' by rw [e]; exact this
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
  let s : Heap := {(p, .int m)}
  let f : Val := .fun .q <| .app incr p
  fun
  | _, rfl => .app₁ (fun v h => v = f ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .app_fun <| triple_incr _ _ _ <| show s = {(p, .int m)} from rfl

/-- `triple_incr_first_derived` -/
example (p q : Loc) (m n : Int) :
  Triple (.app (.app incr_first p) q)
    (.hsingle p m * .hsingle q n)
    fun _ => .hsingle p (m + 1 : Int) * .hsingle q n
:=
  fun
  | _, ⟨_, _, h₁, h₂, h, rfl⟩ => .frame₁ h h₂ <| triple_incr_first' _ _ _ _ h₁

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
  let Q _ := .hsingle p k * .hsingle q (0 : Int)
  fun
  | _, ⟨s₁, s₂, h₁, h₂, h, rfl⟩ => show Eval Q (.app (.app transfer p) q) (s₁ ∪ s₂) from
  let t := .let .m (.get p) <| .let .n (.get .q) <| .let .s (.m + .n) <| .seq (.set p .s) (.set .q 0)
  .app₁ (fun v s => v = Val.fun .q t ∧ s = s₁ ∪ s₂) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => show Eval Q (.app (Val.fun .q t) q) (s₁ ∪ s₂) from
  let t := .let .m (.get p) <| .let .n (.get q) <| .let .s (.m + .n) <| .seq (.set p .s) (.set q 0)
  suffices Eval Q t (s₁ ∪ s₂) from .app_fun this
  .let (fun v => .hpure (v = m) * .hsingle p m * .hsingle q n) (.frame₁ h h₂ <|
    have m₁ : p ∈ s₁ := h₁ ▸ Heap.singleton_mem
    have g₁ : s₁.get p m₁ = m := h₁ ▸ Heap.singleton_get
    .get m₁ ⟨∅, s₁, ⟨g₁, rfl⟩, h₁, s₁.empty_disjoint, s₁.empty_union⟩
  ) fun
  | v, _, ⟨_, s₂, ⟨empty, s₁, hempty, h₁, _, rfl⟩, h₂, h, rfl⟩ =>
  match v, empty, (hempty : ∃ x : v = m, HProp.hempty empty) with
  | _, _, ⟨rfl, rfl⟩ =>
  have h : Disjoint s₁ s₂ := s₁.empty_union ▸ h
  let t := .let .n (.get q) <| .let .s (m + .n) <| .seq (.set p .s) (.set q 0)
  show Eval Q t (∅ ∪ s₁ ∪ s₂) from
  suffices Eval Q t (s₁ ∪ s₂) from s₁.empty_union ▸ this
  .let (fun v => .hsingle p m * (.hpure (v = n) * .hsingle q n)) (.frame₂ h h₁ <|
    have m₂ : q ∈ s₂ := h₂ ▸ Heap.singleton_mem
    have g₂ : s₂.get q m₂ = n := h₂ ▸ Heap.singleton_get
    .get m₂ ⟨∅, s₂, ⟨g₂, rfl⟩, h₂, s₂.empty_disjoint, s₂.empty_union⟩
  ) fun
  | v, _, ⟨s₁, _, h₁, ⟨empty, s₂, hempty, h₂, _, rfl⟩, h, rfl⟩ =>
  match v, empty, hempty with
  | _, _, ⟨rfl, rfl⟩ =>
  have h : Disjoint s₁ s₂ := s₂.empty_union ▸ h
  let t := .let .s (m + n) <| .seq (.set p .s) (.set q 0)
  show Eval Q t (s₁ ∪ (∅ ∪ s₂)) from
  suffices Eval Q t (s₁ ∪ s₂) from s₂.empty_union ▸ this
  .let (fun v s => v = k ∧ s = s₁ ∪ s₂) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  let t := .seq (.set p k) (.set q 0)
  show Eval Q t (s₁ ∪ s₂) from
  .seq (fun _ => .hsingle p k * .hsingle q n) (
    match s₁, h₁, h with
    | _, rfl, h => .frame₁ h h₂ <| .set Heap.singleton_mem Heap.singleton_insert
  ) fun
  | _, _, ⟨s₁, s₂, h₁, h₂, h, rfl⟩ =>
  show Eval Q (.set q 0) (s₁ ∪ s₂) from
  match s₂, h₂, h with
  | _, rfl, h => .frame₂ h h₁ <| .set Heap.singleton_mem Heap.singleton_insert

theorem triple_transfer_aliased (p : Loc) (m : Int) :
  Triple (.app (.app transfer p) p)
    (.hsingle p m)
    fun _ => .hsingle p (0 : Int)
:=
  let s : Heap := {(p, .int m)}
  let f : Val := .fun .q <|
    .let .m (.get p) <|
    .let .n (.get .q) <|
    .let .s (.m + .n) <|
    .seq (.set p .s) (.set .q 0)
  fun
  | _, rfl => .app₁ (fun v h => v = f ∧ h = s) id (.app_fun <| .fun ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  .app_fun <| .let (fun v h => v = m ∧ h = s) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  .let (fun v h => v = m ∧ h = s) (.get Heap.singleton_mem ⟨Heap.singleton_get, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ => .let (fun v h => v = m + m ∧ h = s) (.add ⟨rfl, rfl⟩) fun
  | _, _, ⟨rfl, rfl⟩ =>
  .seq (fun _ => .hsingle p (m + m)) (.set Heap.singleton_mem Heap.singleton_insert) fun
  | _, _, rfl => .set Heap.singleton_mem Heap.singleton_insert

end Basic
