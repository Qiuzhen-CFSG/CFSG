module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.GroupTheory.PGroup

/-!
# Two-subgroups of the concrete L₄(2) model

The proved exceptional equivalence L₄(2) ≃ A₈ gives order 20160 = 64 · 315.
Lagrange's theorem then bounds every faithfully embedded two-group by 64.
This supplies the numerical obstruction after A₃ recognition in
Aschbacher--Smith, *The Classification of Quasithin Groups*, §14.4,
printed p. 1012. No enumeration of Sylow subgroups is needed.
-/

@[expose] public section

namespace Matrix.PSL4Two

/-- The concrete projective four-dimensional binary group has order 20160. -/
theorem card_model :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Nat.card_congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toEquiv,
    nat_card_alternatingGroup, Nat.card_fin]
  decide

/-- Every faithfully embedded two-group in the actual L₄(2) model has order at most 64. -/
theorem card_twoGroup_le_sixtyFour
    {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (f : T →* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))
    (hf : Function.Injective f) : Nat.card T ≤ 64 := by
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hd : 2 ^ n ∣ 20160 := by
    rw [← hn, ← card_model]
    exact Subgroup.card_dvd_of_injective f hf
  have hc : Nat.Coprime (2 ^ n) 315 :=
    (by decide : Nat.Coprime 2 315).pow_left n
  have hd64 : 2 ^ n ∣ 64 := hc.dvd_of_dvd_mul_right (by simpa using hd)
  rw [hn]
  exact Nat.le_of_dvd (by decide) hd64

end Matrix.PSL4Two
