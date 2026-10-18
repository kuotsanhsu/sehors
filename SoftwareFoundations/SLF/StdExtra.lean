import Std.Data.TreeSet
import Std.Data.ExtTreeSet

section

variable {α β} [Membership α β]
def Disjoint (b₁ b₂ : β) : Prop := ∀ a, a ∈ b₁ → a ∈ b₂ → False
theorem Disjoint.symm {b₁ b₂ : β} : Disjoint b₁ b₂ → Disjoint b₂ b₁ | h, h' => flip (h h')

end

section

universe u
variable {α : Type u} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

namespace Std.DTreeMap

variable {β} {t t₁ t₂ t₃ : DTreeMap α β cmp}
theorem Equiv.union_empty : t ∪ ∅ ~m t :=
  of_forall_get?_eq fun _ => get?_union
theorem Equiv.empty_union : ∅ ∪ t ~m t :=
  of_forall_get?_eq fun _ => get?_union.trans Option.or_none
theorem Equiv.union_assoc : t₁ ∪ t₂ ∪ t₃ ~m t₁ ∪ (t₂ ∪ t₃) :=
  of_forall_get?_eq fun k => by simp only [get?_union, Option.or_assoc]
theorem union_get?_eq_some_get {k} (h₂ : k ∈ t₂) : (t₁ ∪ t₂).get? k = some (t₂.get k h₂) :=
  let v₂ := some (t₂.get k h₂)
  calc (t₁ ∪ t₂).get? k
    _ = (t₂.get? k).or _ := get?_union
    _ = v₂.or _ := congrArg (Option.or · _) (get?_eq_some_get h₂)
    _ = v₂ := rfl
theorem union_get?_eq_none {k} (h₁ : k ∉ t₁) (h₂ : k ∉ t₂) : (t₁ ∪ t₂).get? k = none :=
  get?_eq_none fun h : k ∈ t₁ ∪ t₂ => h₂ <| mem_of_mem_union_of_not_mem_left h h₁
theorem union_get?_comm_of_disjoint {k} (h₁ : k ∈ t₁) (h₂ : k ∉ t₂) : (t₁ ∪ t₂).get? k = (t₂ ∪ t₁).get? k :=
  calc (t₁ ∪ t₂).get? k
   _ = (t₂.get? k).or (t₁.get? k) := get?_union
   _ = none.or (t₁.get? k) := congrArg (Option.or · _) <| get?_eq_none h₂
   _ = none.or (some (t₁.get k h₁)) := congrArg none.or <| get?_eq_some_get h₁
   _ = some (t₁.get k h₁) := rfl
   _ = (t₂ ∪ t₁).get? k := union_get?_eq_some_get h₁ |>.symm
theorem Equiv.union_comm (h : ∀ k (h₁ : k ∈ t₁) (h₂ : k ∈ t₂), t₁.get k h₁ = t₂.get k h₂) : t₁ ∪ t₂ ~m t₂ ∪ t₁ :=
  of_forall_get?_eq fun k =>
    match (inferInstance : Decidable (k ∈ t₁)), (inferInstance : Decidable (k ∈ t₂)) with
    | isTrue (h₁ : k ∈ t₁), isTrue (h₂ : k ∈ t₂) =>
      calc (t₁ ∪ t₂).get? k
       _ = some (t₂.get k h₂) := union_get?_eq_some_get h₂
       _ = some (t₁.get k h₁) := congrArg some (h k h₁ h₂).symm
       _ = (t₂ ∪ t₁).get? k := union_get?_eq_some_get h₁ |>.symm
    | isTrue (h₁ : k ∈ t₁), isFalse (h₂ : k ∉ t₂) => union_get?_comm_of_disjoint h₁ h₂
    | isFalse (h₁ : k ∉ t₁), isTrue (h₂ : k ∈ t₂) => union_get?_comm_of_disjoint h₂ h₁ |>.symm
    | isFalse (h₁ : k ∉ t₁), isFalse (h₂ : k ∉ t₂) =>
      (union_get?_eq_none h₁ h₂).trans (union_get?_eq_none h₂ h₁).symm
theorem Equiv.union_comm_of_disjoint (h : Disjoint t₁ t₂) : t₁ ∪ t₂ ~m t₂ ∪ t₁ :=
  union_comm fun k h₁ h₂ => (h k h₁ h₂).elim

end Std.DTreeMap

namespace Std.ExtDTreeMap

variable {β} {t t₁ t₂ t₃ : ExtDTreeMap α β cmp}
theorem union_empty : t ∪ ∅ = t :=
  t.inductionOn fun _ => sound .union_empty
theorem empty_union : ∅ ∪ t = t :=
  t.inductionOn fun _ => sound .empty_union
theorem union_assoc : t₁ ∪ t₂ ∪ t₃ = t₁ ∪ (t₂ ∪ t₃) :=
  t₁.inductionOn fun _ => t₂.inductionOn fun _ => t₃.inductionOn fun _ => sound .union_assoc
theorem union_comm : (∀ k (h₁ : k ∈ t₁) (h₂ : k ∈ t₂), t₁.get k h₁ = t₂.get k h₂) → t₁ ∪ t₂ = t₂ ∪ t₁ :=
  inductionOn₂ t₁ t₂ fun s₁ s₂ h => sound <| show (s₁ ∪ s₂).Equiv (s₂ ∪ s₁) from .union_comm h
theorem union_comm_of_disjoint (h : Disjoint t₁ t₂) : t₁ ∪ t₂ = t₂ ∪ t₁ :=
  union_comm fun k h₁ h₂ => (h k h₁ h₂).elim

end Std.ExtDTreeMap

namespace Std.TreeMap.Equiv

variable {β} {t t₁ t₂ t₃ : TreeMap α β cmp}
theorem union_empty : t ∪ ∅ ~m t :=
  ⟨.union_empty⟩
theorem empty_union : ∅ ∪ t ~m t :=
  ⟨.empty_union⟩
theorem union_assoc : t₁ ∪ t₂ ∪ t₃ ~m t₁ ∪ (t₂ ∪ t₃) :=
  ⟨.union_assoc⟩
example (h : Disjoint t₁ t₂) : t₁ ∪ t₂ ~m t₂ ∪ t₁ :=
  of_forall_constGet?_eq fun k =>
    if h₁ : k ∈ t₁ then
      have h₂ : k ∉ t₂ := h k h₁
      (getElem?_union_of_not_mem_right h₂).trans (getElem?_union_of_not_mem_left h₂).symm
    else
      (getElem?_union_of_not_mem_left h₁).trans (getElem?_union_of_not_mem_right h₁).symm
theorem union_comm_of_disjoint (h : Disjoint t₁ t₂) : t₁ ∪ t₂ ~m t₂ ∪ t₁ :=
  ⟨.union_comm_of_disjoint h⟩

end Std.TreeMap.Equiv


namespace Std.TreeSet.Equiv

variable {s s₁ s₂ s₃ : TreeSet α cmp}
theorem union_empty : s ∪ ∅ ~m s :=
  ⟨.union_empty⟩
theorem empty_union : ∅ ∪ s ~m s :=
  ⟨.empty_union⟩
theorem union_assoc : s₁ ∪ s₂ ∪ s₃ ~m s₁ ∪ (s₂ ∪ s₃) :=
  ⟨.union_assoc⟩
theorem union_comm_of_disjoint (h : Disjoint s₁ s₂) : s₁ ∪ s₂ ~m s₂ ∪ s₁ :=
  ⟨.union_comm_of_disjoint h⟩

end Std.TreeSet.Equiv

namespace Std.ExtTreeMap

variable {β} {t t₁ t₂ t₃ : ExtTreeMap α β cmp}
theorem union_empty : t ∪ ∅ = t :=
  congrArg mk ExtDTreeMap.union_empty
theorem empty_union : ∅ ∪ t = t :=
  congrArg mk ExtDTreeMap.empty_union
theorem union_assoc : t₁ ∪ t₂ ∪ t₃ = t₁ ∪ (t₂ ∪ t₃) :=
  congrArg mk ExtDTreeMap.union_assoc
theorem union_comm_of_disjoint (h : Disjoint t₁ t₂) : t₁ ∪ t₂ = t₂ ∪ t₁ :=
  congrArg mk <| ExtDTreeMap.union_comm_of_disjoint h

end Std.ExtTreeMap

namespace Std.ExtTreeSet

variable {s s₁ s₂ s₃ : ExtTreeSet α cmp}
theorem union_empty : s ∪ ∅ = s :=
  congrArg mk ExtTreeMap.union_empty
theorem empty_union : ∅ ∪ s = s :=
  congrArg mk ExtTreeMap.empty_union
theorem union_assoc : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  congrArg mk ExtTreeMap.union_assoc
theorem union_comm_of_disjoint (h : Disjoint s₁ s₂) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
  congrArg mk <| ExtTreeMap.union_comm_of_disjoint h

end Std.ExtTreeSet

end

/-
class inductive GhostNat α : α → Prop
  | zero (a : α) : GhostNat α a
  | succ (f : α → α) (a : α) : GhostNat α a → GhostNat α (f a)

instance GhostNat.ofNat : (n : Nat) → GhostNat Nat n
  | 0 => zero 0
  | n + 1 => succ _ n (ofNat n)
-/
