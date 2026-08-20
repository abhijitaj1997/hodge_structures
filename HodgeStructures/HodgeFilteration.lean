import HodgeStructures.BaseModification

open TensorProduct DirectSum

structure RealHodgeFilteration (V : Type u) (n : ℤ) [AddCommGroup V] [Module ℝ V] where
  F : ℤ → Submodule ℂ (V[ℝ,ℂ])
  filteration : Antitone F
  internal_sum : ∀ p : ℤ, IsInternal ![toReal (F p),
                 Submodule.map (spaceConj V) (toReal (F (n - p + 1)))]

#min_imports
