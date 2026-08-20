import Mathlib.Analysis.InnerProductSpace.Basic


universe u₁ u₂ u₃
open TensorProduct

section BaseChange

variable {R : Type u₁} {M : Type u₂} {S : Type u₃}
variable [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]

/- For a module `M` over a ring `R` and and `R`-algebra `S`, the base change of
`M` to `S` is the `S`-module `S ⊗[R] M` is the base change of `M` to `S`. This
module is denote by `M[R,S]`-/
notation:100 M:100 "["R","S"]" => S ⊗[R] M

noncomputable def twisted_mul_tensor_right {N : Type*} [AddCommGroup N]
    [Module R N] (φ : M →ₗ[R] N) (f : S →ₐ[R] S) (s : S) : M →ₗ[R] N[R,S] where
  toFun m := (f s) ⊗ₜ (φ m)
  map_add' := by
    intro m₁ m₂
    rw[map_add, tmul_add]
  map_smul' := by
    intro r m
    simp

noncomputable def twisted_basechange_lift {N : Type*} [AddCommGroup N]
    [Module R N] (φ : M →ₗ[R] N) (f : S →ₐ[R] S) : S →ₗ[R] M →ₗ[R] N[R,S] where
  toFun s := twisted_mul_tensor_right φ f s
  map_add' := by
    intro s₁ s₂
    ext
    simp[twisted_mul_tensor_right, add_tmul]
  map_smul' := by
    intro r s
    ext
    simp[twisted_mul_tensor_right, map_smul, smul_tmul]

noncomputable def twisted_basechange_map {N : Type*} [AddCommGroup N]
    [Module R N] (φ : M →ₗ[R] N) (f : S →ₐ[R] S) : M[R,S] →ₗ[R] N[R,S]
  := TensorProduct.lift (twisted_basechange_lift φ f)

noncomputable def basechange_map (S : Type u₃) [CommRing S] [Algebra R S]
    {N : Type*} [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) : M[R,S] →ₗ[S] N[R,S] where
  toFun := by
    exact (twisted_basechange_map φ (AlgHom.id R S)).toFun
  map_add' := by simp
  map_smul' := by
    intro s m
    simp
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul s' m => have : s • (s' ⊗ₜ[R] m) = (s * s') ⊗ₜ[R] m := by rfl
                   simp[this]
                   rfl
    | add _ _ h₁ h₂ => simp[smul_add, map_add, h₁, h₂]

noncomputable def extend (N : Submodule R M) : Submodule S (M[R,S])
  := Submodule.map (basechange_map S (N.subtype)) ⊤

end BaseChange







section RealToComplex

--I NEED TO UNDERSTAND WHY LEAN FORCED ME TO WRITE NONCOMPUTABLE IN THIS DOC

/-Given a real vector space `V`, this defines a conjugation map on the complex vector space
`V[ℝ, ℂ] = ℂ ⨂ V` as `z ⨂ v ↦ (conj z) ⨂ v` as a map of real vector spaces-/
noncomputable def spaceConj (V : Type*) [AddCommGroup V] [Module ℝ V] :
    V[ℝ, ℂ] →ₗ[ℝ] V[ℝ, ℂ] := twisted_basechange_map (LinearMap.id : V →ₗ[ℝ] V) Complex.conjAe



theorem real_extension {V : Type*} [AddCommGroup V] [Module ℝ V] (W₁ : Submodule ℂ (V[ℝ,ℂ]))
  (self_conj : 1 = 1) : ∃ W : Submodule ℝ V, W[ℝ,ℂ] = W₁ := by

  sorry

def toReal {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) : Submodule ℝ V where
  carrier := W
  add_mem' := W.add_mem'
  zero_mem' := W.zero_mem'
  smul_mem' := by
    intro x v hv
    apply W.smul_mem'
    exact hv

end RealToComplex
