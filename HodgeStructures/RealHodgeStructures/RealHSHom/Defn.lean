import HodgeStructures.RealHodgeStructures.Defn

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
