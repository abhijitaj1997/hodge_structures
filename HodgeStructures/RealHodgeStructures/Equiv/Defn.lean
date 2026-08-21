import HodgeStructures.RealHodgeStructures.RealHSHom.Defn

variable {V₁ : Type u} [AddCommGroup V₁] [Module ℝ V₁]
variable {V₂ : Type v} [AddCommGroup V₂] [Module ℝ V₂]

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

#min_imports
