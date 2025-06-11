import MerkleInheritance.Basic

namespace MerkleHash
open MerkleInheritance.Tree

-- Abstract Hash function
abbrev Hash := UInt64
instance : Hashable Hash := inferInstance
instance : DecidableEq Hash := inferInstance
instance : Repr Hash := inferInstance

def defaultHash : Hash := 0x00

instance [Hashable α] : Hashable (Tree α) where
  hash
    | Tree.leaf x => hash [0x00, hash x]
    | Tree.node l r => hash [0x01, hash l, hash r]

/-- Build a (roughly) balanced binary tree from a nonempty list of leaves. -/
def listToTree : List Hash → Tree Hash
  | []       => Tree.leaf defaultHash
  | [x]      => Tree.leaf x
  | xs       =>
    let mid := xs.length / 2
    let l   := xs.take mid
    let r   := xs.drop mid
    Tree.node (listToTree l) (listToTree r)
termination_by xs => xs.length
decreasing_by
  · -- First recursive call: prove `l.length < xs.length`
    simp only [List.length_take]
    have h_pos : 1 < xs.length := by
      -- Since we're not in the [] or [x] cases, xs.length ≥ 2
      by_contra h
      push_neg at h
      interval_cases xs.length
      · -- xs.length = 0 case
        have : xs = [] := List.eq_nil_of_length_eq_zero rfl
        simp [this]
      · -- xs.length = 1 case
        have : ∃ a, xs = [a] := List.eq_cons_of_length_one rfl
        obtain ⟨a, ha⟩ := this
        simp [ha]

    have h_le : mid ≤ xs.length := Nat.div_le_self xs.length 2
    rw [Nat.min_eq_left h_le]

    -- Now prove mid < xs.length
    dsimp [mid]

    exact Nat.div_lt_self (Nat.zero_lt_of_lt h_pos) (by norm_num)

  · -- Second recursive call: prove `r.length < xs.length`
    simp only [List.length_drop]
    have h_pos : 1 < xs.length := by
      by_contra h
      push_neg at h
      have h_le_one : xs.length ≤ 1 := h
      cases' Nat.lt_or_eq_of_le h_le_one with h_zero h_one
      · have h_eq_zero : xs.length = 0 := Nat.eq_zero_of_lt h_zero
        have : xs = [] := List.eq_nil_of_length_eq_zero h_eq_zero
        cases xs <;> simp
      · have : ∃ a, xs = [a] := List.exists_cons_of_length_one h_one
        obtain ⟨a, ha⟩ := this
        rw [ha]
        simp

    have h_mid_pos : 0 < mid := by
      dsimp [mid]
      exact Nat.div_pos h_pos (by norm_num : 0 < 2)

    exact Nat.sub_lt_self (Nat.zero_lt_of_lt h_pos) h_mid_pos

  · -- Second recursive call: prove `r.length < xs.length`
    simp only [List.length_drop]
    have h_pos : 1 < xs.length := by
      by_contra h
      push_neg at h
      have h_le_one : xs.length ≤ 1 := h
      cases' Nat.lt_or_eq_of_le h_le_one with h_zero h_one
      · have h_eq_zero : xs.length = 0 := Nat.eq_zero_of_lt h_zero
        have : xs = [] := List.eq_nil_of_length_eq_zero h_eq_zero
        cases xs <;> simp
      · have : ∃ a, xs = [a] := List.exists_cons_of_length_one h_one
        obtain ⟨a, ha⟩ := this
        rw [ha]
        simp

    have h_mid_pos : 0 < mid := by
      dsimp [mid]
      exact Nat.div_pos h_pos (by norm_num : 0 < 2)

    exact Nat.sub_lt_self (Nat.zero_lt_of_lt h_pos) h_mid_pos

  · -- Second recursive call: prove `r.length < xs.length`
    simp only [List.length_drop]
    have h_pos : 1 < xs.length := by
      by_contra h
      push_neg at h
      interval_cases xs.length
      · have : xs = [] := List.eq_nil_of_length_eq_zero rfl
        simp [this]
      · have : ∃ a, xs = [a] := List.eq_cons_of_length_one rfl
        obtain ⟨a, ha⟩ := this
        simp [ha]

    have h_mid_pos : 0 < mid := by
      dsimp [mid]
      exact Nat.div_pos h_pos (by norm_num : 0 < 2)

    exact Nat.sub_lt_self (Nat.zero_lt_of_lt h_pos) h_mid_pos


def splitList : List α → Nat → (List α × List α)
| [], _ => (([] : List α), ([] : List α))
| x::xs, 0 => ([], x::xs)
| x::xs, n+1 =>
  let (l, r) := splitList xs n
  (x::l, r)

theorem splitInHalf_left_shorter (xs : List α) (n : Nat) :
  (splitList xs n).1.length ≤ xs.length := by
  induction xs generalizing n <;> simp [splitList] <;>
  cases n <;> simp [splitList] <;>
  cases splitList xs n <;> simp

def merkleHash : Tree Hash → Hash
  | Tree.leaf x => hash [0x00, x]
  | Tree.node l r => hash [0x01, merkleHash l, merkleHash r]

end MerkleHash
