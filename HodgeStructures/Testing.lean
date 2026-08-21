import HodgeStructures.RealHodgeStructures.Basic




variable {V₁ : Type u} [AddCommGroup V₁] [Module ℝ V₁] (v w : V₁)
variable {V₂ : Type v} [AddCommGroup V₂] [Module ℝ V₂]
variable (h₁ : RealHodgeStructure V₁) (h₂ : RealHodgeStructure V₂)
variable (f : h₁ →ₕₛ h₂) (f' : RealHSHom h₁ h₂)

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

#check (LinearMap.id : V₁ →ₗ[ℝ] V₁)
#check (LinearEquiv.refl ℝ V₁ : V₁ ≃ₗ[ℝ] V₁)

example : (LinearEquiv.refl ℝ V₁ : V₁ →ₗ[ℝ] V₁) = (LinearMap.id : V₁ →ₗ[ℝ] V₁)
    := rfl


variable (F : h₁ ≃ₕₛ h₂)

#check F
#check F.toRealHSHom
#check F.toLinearMap
#check (F.toRealHSHom : RealHSHom h₁ h₂)
#check ((F : RealHSHom h₁ h₂) : V₁ → V₂)

#check F
#check (F : h₁ →ₕₛ h₂)
#check ((F : h₁ →ₕₛ h₂) : h₁ →ₕₛ h₂)
#check ((F : h₁ →ₕₛ h₂) : V₁ → V₂)
#check RealHSEquiv.toRealHSHom

section

variable [AddCommGroup V] [Module ℝ V] (i : V ≃ₗ[ℝ] V)
#check (i : V →ₗ[ℝ] V)


#check LinearEquiv.toLinearMap
#check LinearEquiv.toAddEquiv
#check LinearMap (RingHom.id ℝ) V₁ V₂
#check LinearEquiv.right_inv

def dfsdjl : LinearEquiv (RingHom.id ℝ) V₁ V₂ where
  toFun := by sorry
  map_add' := by sorry
  map_smul' := by sorry
  invFun := by sorry -----------------
  left_inv := by sorry
  right_inv := by sorry

def sjdfl : RealHSEquiv h₁ h₂ where
  toFun := by sorry
  map_add' := by sorry
  map_smul' := by sorry
  component_corespondence := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end
