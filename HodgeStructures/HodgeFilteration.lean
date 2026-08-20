import HodgeStructures.BaseModification
import Mathlib

open TensorProduct


-- Need to create an internal direct sum using `Fin 2`
structure RealHodgeFilteration (V : Type u) [AddCommGroup V] [Module ℝ V] where
  F : ℤ → Submodule ℂ (V[ℝ,ℂ])
  filteration : Antitone F
  internal_sum : ∀ p : ℤ, ℤ
