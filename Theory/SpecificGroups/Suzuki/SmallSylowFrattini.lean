module
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.Frattini.OmegaProducts

/-!
# Sylow involutions in the small Suzuki group

The actual Sz(2) carrier is the faithful five-by-four group. Its standard
cyclic complement has order four and is Sylow; Sylow conjugacy transports
these coordinates to any chosen Sylow subgroup. In C4 every square-one
element is itself a square, so its first omega lies in its Frattini subgroup.

This is precisely the small-model input for the beta exclusion in DGS
(10.7), pp.158--159. The model identification is the existing actual
FiveFour.suzukiZeroEquiv; no nonbinary Suzuki derived formula is used.
-/

public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups

private noncomputable def smallSuzukiSylowEquiv
    (P : Sylow 2 (SuzukiMatrixGroup 0)) : P ≃* FiveFour.Cyclic 4 := by
  let e := FiveFour.suzukiZeroEquiv.symm
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : FiveFour.Cyclic 4 →* FiveFour.Group := SemidirectProduct.inr
  have hf : Function.Injective f := SemidirectProduct.inr_injective
  have hc : Nat.card f.range = 2 ^ (Nat.card FiveFour.Group).factorization 2 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,FiveFour.card]
    change Nat.card (ZMod 4) = _
    rw [Nat.card_zmod]
    decide +kernel
  let R := Sylow.ofCard f.range hc
  exact ((P : Subgroup (SuzukiMatrixGroup 0)).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((T.equiv R).trans (MonoidHom.ofInjective hf).symm)

/-- Every Sz(2) Sylow involution lies in the Sylow Frattini subgroup,
with its original ambient embedding. -/
theorem smallSuzuki_omega_le_frattini (P : Sylow 2 (SuzukiMatrixGroup 0)) :
    omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup 0)) ≤
      (frattini P).map (P : Subgroup (SuzukiMatrixGroup 0)).subtype := by
  let e := smallSuzukiSylowEquiv P
  let : Fact (IsPGroup 2 (FiveFour.Cyclic 4)) := ⟨IsPGroup.of_card (n := 2) (by
    change Nat.card (ZMod 4) = 2^2
    simp)⟩
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  have hs : (e ⟨x,hx⟩)^2 = 1 := by rw [←map_pow,show (⟨x,hx⟩ : P)^2=1 from Subtype.ext hx2,map_one]
  have he : e ⟨x,hx⟩ ∈ frattini (FiveFour.Cyclic 4) := by
    obtain ⟨y,hy⟩ := (show ∀ z : FiveFour.Cyclic 4, z^2=1 → ∃ y, y^2=z by decide +kernel) _ hs
    exact hy ▸ pth_power_mem_frattini_of_isPGroup (p := 2) y
  have hh := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective he
  change e.symm (e (⟨x,hx⟩ : P)) ∈ frattini P at hh
  rw [e.symm_apply_apply] at hh
  exact mem_map_of_mem (P : Subgroup (SuzukiMatrixGroup 0)).subtype hh
end BenderSuzuki.MatrixGroups
