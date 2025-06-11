import MerkleInheritance.Basic
import MerkleHash.Basic

namespace Finalization
open MerkleInheritance
open MerkleHash

-- We will treat HashFunc as a black box for now
abbrev HashFunc := List Hash → Hash

-- Represents an expression tree used for deterministic finalization
inductive HashExpr
  | leaf : Hash → HashExpr
  | pair : HashExpr → HashExpr → HashExpr
  deriving Repr, BEq, Inhabited

-- Convert a tree into an expression of how hashes should be combined
def toExpr : Tree Hash → HashExpr
  | Tree.leaf h => HashExpr.leaf h
  | Tree.node l r => HashExpr.pair (toExpr l) (toExpr r)

-- Evaluate a HashExpr using a HashFunc
def finalizeExpr (h : HashFunc) : HashExpr → Hash
  | HashExpr.leaf x => x
  | HashExpr.pair l r => h [finalizeExpr h l, finalizeExpr h r]

-- Finalize a Merkle tree using a hash function
def finalize : Tree Hash → Hash
| Tree.leaf v   => merkleHash [v]
| Tree.node l r => merkleHash [ finalize l, finalize r ]

-- Helper for extracting leaves from a HashExpr
def flattenExpr : HashExpr → List Hash
  | HashExpr.leaf x => [x]
  | HashExpr.pair l r => flattenExpr l ++ flattenExpr r
