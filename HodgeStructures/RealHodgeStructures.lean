import HodgeStructures.BaseModification
import Mathlib.Algebra.DirectSum.Basic


-- I did not use extends, because I do not want someone passing a
-- that would create two vector space structure on V
-- one from whatever vector space the person started with
-- the other from RealHodgeStructure.toModule
-- Now, you can only pass real vector spaces as arguments

universe u v
open scoped TensorProduct
open DirectSum

section test
variable (V : Type u) [AddCommGroup V] [Module ℝ V] (index : ℤ → ℤ → Subspace ℂ (V[ℝ,ℂ]))
variable (i j : ℤ)

#check toReal (index i j)
#check Submodule.map (spaceConj V) (toReal (index i j))
end test

-- I do not know if the index_conjugate term is defined well
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







section Morphisms

variable {V₁ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
variable {V₂ : Type v} [AddCommGroup V₂] [Module ℝ V₂]

-- Should this be done use extending a Linear map?
-- Or, Should this be done starting form toFun?
-- Morphisms between vector spaces are also group hom (check how it is done
-- there)
structure RealHodgeStructureMorphism (h₁ : RealHodgeStructure V₁) (h₂ : RealHodgeStructure V₂)
    where
  toLinearMap : V₁ →ₗ[ℝ] V₂
  component_corespondence : ∀ p₁ p₂ : ℤ,
    (h₁.index p₁ p₂).map (basechange_map ℂ toLinearMap) ≤ h₂.index p₁ p₂


--notation:25 h₁ " →ₗₕ[" ℝ:25 "] " h₂:0 => LinearMap (RingHom.id R) M M₂
notation:25 h₁ " →ₕₛ " h₂:0 => (RealHodgeStructureMorphism h₁ h₂) -- how does on get ℝ into this?
end Morphisms
