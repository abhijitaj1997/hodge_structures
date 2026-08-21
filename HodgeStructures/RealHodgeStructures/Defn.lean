import HodgeStructures.BaseModification


universe u v
open TensorProduct
open DirectSum


/-
I did not use extends because the question is basically:
"Is a real HS a vector space with a additional properties
or is a real HS on a vector space some structure on the
aforementioned vector space."
And, I went with the latter.

This is because we sometimes need to consider multiple
hodge structures on the same vector space (not just on
the same set). Adding the vector space structure into
the bundle would mean that if I have two terms
`h₁ RealHodgeStructure V`
`h₂ RealHodgeStructure V`
then in the two cases, the underlying vector space
structure on `V` will not be the same
-/
-- I do not know if the index_conjugate term is defined well
-- Should I make it a `fintie dimensional`??

/-- A real Hodge structure on a real vector space `V`, is a direct sum decomposition
of its complexification, indexed by `ℤ × ℤ`, such that the `(p, q)`-th
component of the decompositon is conjugate to the `(q, p)`-th component. -/
@[ext]
structure RealHodgeStructure (V : Type u) [AddCommGroup V] [Module ℝ V] where
  index : ℤ → ℤ → Subspace ℂ (V[ℝ,ℂ])
  internal_sum : IsInternal (fun (p : ℤ × ℤ) => index p.1 p.2)
  index_conjugate : ∀ i j : ℤ, toReal (index j i) = Submodule.map (spaceConj V) (toReal (index i j))

namespace RealHodgeStructure
variable {V : Type u} [AddCommGroup V] [Module ℝ V]

def typ (h : RealHodgeStructure V) : Set (ℤ × ℤ)
    := {p : ℤ × ℤ | h.index p.1 p.2 ≠ ⊥}

-- do we need this?
-- it's like the "is purity a noun or an adverb" debate
def isPure (h : RealHodgeStructure V) : Prop := ∃ n : ℤ, ∀ p ∈ typ h, p.1 + p.2 = n
end RealHodgeStructure


section PureHodgeStructures
variable {V : Type u} [AddCommGroup V] [Module ℝ V]

open RealHodgeStructure
class PureHS (h : RealHodgeStructure V) where
  proof_of_purity : isPure h

end PureHodgeStructures
