namespace MerkleInheritance

instance [Hashable α] : Hashable (List α) := inferInstance

namespace Tree

-- Basic Merkle Tree
inductive Tree (α : Type)
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
deriving Repr, Inhabited, BEq, Hashable

-- ContainsLeaf inductive type to check if a value is in the tree
inductive containsLeaf {α : Type} : Tree α → α → Prop
  | here {x : α} : containsLeaf (Tree.leaf x) x
  | left {l r : Tree α} {v : α} : containsLeaf l v → containsLeaf (Tree.node l r) v
  | right {l r : Tree α} {v : α} : containsLeaf r v → containsLeaf (Tree.node l r) v

def flatten {α : Type} (t : Tree α) : List α :=
  match t with
  | Tree.leaf x => [x]
  | Tree.node l r => flatten l ++ flatten r

-- Hash computation for Tree α
def computeHash {α : Type} [Hashable α] (t : Tree α) : UInt64 :=
  hash (flatten t : List α)

theorem containsLeaf_in_flatten {α : Type} (t : Tree α) (v : α) (h : containsLeaf t v) : v ∈ flatten t :=
  match h with
  | containsLeaf.here => by simp [flatten]
  | containsLeaf.left h₁ => by
    apply List.mem_append_left
    exact containsLeaf_in_flatten _ _ h₁
  | containsLeaf.right h₂ => by
    apply List.mem_append_right
    exact containsLeaf_in_flatten _ _ h₂

/-!
## 6. Structural inclusion in hash
Proves that the hash is a function of the leaves including `v`.
-/

theorem hash_depends_on_leaf {α : Type} [Hashable α] :
  ∀ (t : Tree α) (v : α), containsLeaf t v → ∃ (hs : List α), v ∈ hs ∧ computeHash t = hash hs
  | t, v, h =>
    let hs : List α := flatten t
    ⟨hs, containsLeaf_in_flatten t v h, rfl⟩

end Tree

end MerkleInheritance
