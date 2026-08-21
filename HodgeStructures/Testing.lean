import HodgeStructures.RealHodgeStructures

variable {V₁ : Type u} [AddCommGroup V₁] [Module ℝ V₁] (v w : V₁)
variable {V₂ : Type v} [AddCommGroup V₂] [Module ℝ V₂]
variable (h₁ : RealHodgeStructure V₁) (h₂ : RealHodgeStructure V₂)
variable (f : h₁ →ₕₛ h₂)

#check f
#check (RealHSHom.toLinearMap f)

#check (f : V₁ → V₂)
#check (f : V₁ →+ V₂)
#check (f : V₁ →ₗ[ℝ] V₂)

#check f 0
#check f.toLinearMap.map_smulₛₗ

example : v + w = w + v := by
  exact add_comm v w

#check V₁ ≃ₗ[ℝ] V₂
#check V₁ ≃+ V₂

variable (g : V₁ ≃ₗ[ℝ] V₂)
#check g

#check (g : V₁ →ₗ[ℝ] V₂)
