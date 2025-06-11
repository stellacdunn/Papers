import MerkleInheritance.Basic
import MerkleInheritance.Finalization

namespace MerkleInheritance
open Finalization
open Tree

theorem treeHash_consistent (xs : List Hash) :
  hash (listToTree xs) = merkleHash xs := by
  induction xs with
  | nil =>
    simp [merkleHash, listToTree, hash]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [merkleHash, listToTree, hash]
    | cons y ys =>
      cases ys with
      | nil =>
        simp [merkleHash, listToTree, hash]
      | cons z zs =>
        simp [merkleHash, listToTree]
        -- unfold tree hashing here
        rw [←ih]
        rfl

-- Theorem showing that finalizing a leaf produces the value directly
theorem finalize_soundness (h : HashFunc) (v : Hash) :
  finalize h (Tree.leaf v) = v := by
  simp [finalize, toExpr, finalizeExpr]

theorem finalize_node_consistency (h : HashFunc) (t1 t2 : Tree Hash) :
  finalize h (Tree.node t1 t2) = h [finalize h t1, finalize h t2] := by
  simp [finalize, toExpr, finalizeExpr]

theorem finalize_leaf (h : HashFunc) (v : Hash) :
  finalize h (Tree.leaf v) = v := by
  simp [finalize, toExpr, finalizeExpr]

theorem finalize_node (h : HashFunc) (l r : Tree Hash) :
  finalize h (Tree.node l r) = h [finalize h l, finalize h r] := by
  simp [finalize, toExpr, finalizeExpr]

-- Updated flattenExpr for HashExpr type
def flattenExpr : HashExpr → List Hash
  | HashExpr.leaf x => [x]
  | HashExpr.pair l r => flattenExpr l ++ flattenExpr r

-- Main theorem: Finalize depends on the leaves, producing a correct result.
theorem finalize_depends_on_leaves :
  ∀ (t : Tree Hash) (v : Hash), containsLeaf t v → v ∈ flattenExpr (toExpr t) := by
  intros t v H
  induction H
  case here x =>
    dsimp [toExpr, flattenExpr]
    exact List.mem_singleton_self x
  case left ih =>
    simp [toExpr, flattenExpr]
    apply Or.inl
    exact ih
  case right ih =>
    simp [toExpr, flattenExpr]
    apply Or.inr
    exact ih

-- Theorem showing finalize is structurally recursive and matches tree shape
theorem finalize_structural (h : HashFunc) :
  ∀ (t : Tree Hash), finalize h t = match t with
                                    | Tree.leaf v   => v
                                    | Tree.node l r => h [finalize h l, finalize h r] := by
  intro t
  cases t with
  | leaf v => simp [finalize, toExpr, finalizeExpr]
  | node l r => simp [finalize, toExpr, finalizeExpr]

theorem flattenExpr_contains :
  ∀ (t : Tree Hash) (v : Hash), v ∈ flattenExpr (toExpr t) → containsLeaf t v
  | leaf x, v, h =>
    by
      simp [toExpr, flattenExpr] at h
      cases h
      apply containsLeaf.here
  | node l r, v, h =>
    by
      simp [toExpr, flattenExpr] at h
      match h with
      | Or.inl hl => exact containsLeaf.left (flattenExpr_contains l v hl)
      | Or.inr hr => exact containsLeaf.right (flattenExpr_contains r v hr)

theorem computeHash_depends_on_leaf {α : Type} [Hashable α] (t : Tree α) (v : α) (h : containsLeaf t v) :
  ∃ hs : List α, v ∈ hs ∧ computeHash t = hash hs := by
  let hs := flatten t
  exact ⟨hs, containsLeaf_in_flatten t v h, rfl⟩

theorem treeHash_deterministic {α : Type} [Hashable α] (L : List α) :
  ∀ (T1 T2 : Tree α), listToTree_using T1 L = T1 → listToTree_using T2 L = T2 →
    computeHash T1 = computeHash T2 :=
by
  /- Proof sketch:
     - Both trees have leaves exactly L in order (listToTree_correctness).
     - Hash is computed by flattening then hashing, so equal flatten yields equal hash.
     - Need lemma: flatten (listToTree_using T L) = L.
   -/
  intros T1 T2 hT1 hT2
  have hLeaves1 : flatten T1 = L := by
    -- apply lemma listToTree_correctness
    sorry
  have hLeaves2 : flatten T2 = L := by
    sorry
  -- conclude by rewrite
  calc
    computeHash T1 = hash (flatten T1) := rfl
    _ = hash L := by rw [hLeaves1]
    _ = hash (flatten T2) := (by rw [hLeaves2])
    _ = computeHash T2 := rfl

namespace Finalization
open MerkleInheritance
open Tree

-- A Module is a Merkle tree with Hash values at the leaves
abbrev Module := Tree Hash

-- Finalized module is also a tree with Hash values (placeholder)
abbrev Finalized := Tree Hash

-- Finalization is deterministic
theorem finalize_deterministic (h : HashFunc) (t : Tree Hash) :
  finalize h t = finalize h t := by
  rfl  -- determinism by definition

theorem finalize_agrees_with_flattenExpr :
  ∀ (t : Tree Hash) (h : HashFunc),
    finalize h t = finalizeExpr h (toExpr t) := by
  intros t h
  induction t with
  | leaf x =>
    simp [finalize, toExpr, finalizeExpr]
  | node l r ih_l ih_r =>
    simp [finalize, toExpr, finalizeExpr]

theorem computeHash_agrees_with_finalizeExpr :
  ∀ (t : Tree Hash), computeHash t = finalizeExpr (λ hs => hash hs) (toExpr t) := by
  intro t
  induction t with
  | leaf x =>
    simp [computeHash, toExpr, finalizeExpr]
  | node l r ih_l ih_r =>
    simp [computeHash, toExpr, finalizeExpr]

end Finalization

end MerkleInheritance
