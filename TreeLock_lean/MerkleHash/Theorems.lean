import MerkleHash.Basic

namespace MerkleHash

@[simp]
theorem merkleHash_nil : merkleHash [] = defaultHash := by
  rfl

@[simp]
theorem merkleHash_singleton (x : Hash) : merkleHash [x] = hash [0x00, x] := by
  rfl

@[simp]
theorem merkleHash_pair (l r : Hash) : merkleHash [l, r] = hash [0x01, hash [0x00, l], hash [0x00, r]] := by
  simp [merkleHash]


end MerkleHash
