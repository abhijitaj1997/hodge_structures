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







section Morphisms

variable {V₁ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
variable {V₂ : Type v} [AddCommGroup V₂] [Module ℝ V₂]

-- Should this be done use extending a Linear map?
-- Or, Should this be done starting form toFun?
-- Morphisms between vector spaces are also group hom (check how it is done
-- there)
/-- A morphism between real Hodge structures `h₁` and `h₂`, is a linear map
between the base vector spaces, such that the induced map between the
complexifications respects the direct sum decopositon. -/
@[ext]
structure RealHSHom (h₁ : RealHodgeStructure V₁) (h₂ : RealHodgeStructure V₂)
    extends LinearMap (RingHom.id ℝ) V₁ V₂ where
  component_corespondence : ∀ p₁ p₂ : ℤ,
    (h₁.index p₁ p₂).map (basechange_map ℂ toLinearMap) ≤ h₂.index p₁ p₂

/-- `h₁ →ₕₛ h₁` is the type of real Hodge structures morphisms from `h₁` to `h₂` -/
notation:25 h₁ " →ₕₛ " h₂:0 => (RealHSHom h₁ h₂) -- how does on get ℝ into this?


instance {h₁ : RealHodgeStructure V₁} {h₂ : RealHodgeStructure V₂}
    : FunLike (RealHSHom h₁ h₂) V₁ V₂ where
  coe f := ((RealHSHom.toLinearMap f) : V₁ → V₂)
  coe_injective := fun f₁ f₂ h => (by ext ; simp[h])

instance : LinearMapClass (RealHSHom h₁ h₂) ℝ V₁ V₂ where
  map_add := fun f => f.toLinearMap.map_add
  map_smulₛₗ := fun f => f.toLinearMap.map_smulₛₗ

-- I probably need to switch this to an equivalence!
-- check out how it is done for other algebraic structures
set_option linter.style.show false -- to avoid a warning for `show`
def RealHSHom.id (h : RealHodgeStructure V₁) : RealHSHom h h where
  toFun := ((LinearMap.id : V₁ →ₗ[ℝ] V₁) : V₁ → V₁)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  component_corespondence := by
    intro p₁ p₂ v h
    rcases h with ⟨w, hw, rfl⟩
    show (basechange_map ℂ LinearMap.id) w ∈ h.index p₁ p₂
    rwa[basechange_map_id w]

lemma RealHSHom.map_apply {h₁ : RealHodgeStructure V₁} {h₂ : RealHodgeStructure V₂}
    (f : h₁ →ₕₛ h₂) (v : V₁) : f v = f.toFun v := rfl

lemma RealHSHom.id_apply (h : RealHodgeStructure V₁) (v : V₁)
    : RealHSHom.id h v = v := rfl

-- *Is this enough??*
structure RealHSEquiv (h₁ : RealHodgeStructure V₁) (h₂ : RealHodgeStructure V₂)
    extends RealHSHom h₁ h₂, V₁ ≃ₗ[ℝ] V₂

instance {h₁ : RealHodgeStructure V₁} {h₂ : RealHodgeStructure V₂}
    : Coe (RealHSEquiv h₁ h₂) (RealHSHom h₁ h₂) where
    coe f := f.toRealHSHom

attribute [coe] RealHSEquiv.toRealHSHom

notation:50 h₁ " ≃ₕₛ " h₂ => RealHSEquiv h₁ h₂

/-- The morphism of real Hodge structure underlying an equivalence
real of Hodge structures -/
add_decl_doc RealHSEquiv.toRealHSHom

-- I NEED TO DEFINE  A `RealHSHomClass`

end Morphisms

#min_imports
