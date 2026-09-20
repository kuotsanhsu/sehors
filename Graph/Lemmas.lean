namespace List

variable {α} {b : α} {as : List α} {i : Fin as.length}

theorem take_append_get_cons_drop : as.take i ++ as.get i :: as.drop (i + 1) = as :=
  as.drop_eq_getElem_cons i.isLt ▸ as.take_append_drop i

theorem set_take_append_cons_drop : as.set i b = as.take i ++ b :: as.drop (i + 1) :=
  trans as.set_eq_take_append_cons_drop (ite_eq_left i.isLt)

end List

section

variable {b : Nat}

theorem List.get_add_set_sum {as : List Nat} {i : Fin as.length} :
    as.get i + (as.set i b).sum = b + as.sum :=
  let xs := as.take i
  let a := as.get i
  let ys := as.drop (i + 1)
  let bs := as.set i b
  calc (a :: bs).sum
   _ = (a :: (xs ++ b :: ys)).sum := set_take_append_cons_drop ▸ rfl
   _ = (a :: xs ++ b :: ys).sum := rfl
   _ = a + xs.sum + (b + ys.sum) := List.sum_append_nat
   _ = b + xs.sum + (a + ys.sum) := by ac_rfl
   _ = (b :: xs).sum + (a :: ys).sum := rfl
   _ = (b :: (xs ++ a :: ys)).sum := List.sum_append_nat.symm
   _ = (b :: as).sum := take_append_get_cons_drop ▸ rfl

theorem Array.get_add_set_sum {as : Array Nat} {i : Fin as.size} :
    as[i] + (as.set i b).sum = b + as.sum :=
  let a := as[i]
  let bs := as.set i b
  calc a + bs.sum
   _ = a + bs.toList.sum := congrArg a.add bs.sum_toList.symm
   _ = b + as.toList.sum := as.toList.get_add_set_sum
   _ = b + as.sum := congrArg b.add as.sum_toList

theorem Vector.get_add_set_sum {n} {as : Vector Nat n} {i : Fin as.size} :
    as.get i + (as.set i b).sum = b + as.sum :=
  as.toArray.get_add_set_sum

end
