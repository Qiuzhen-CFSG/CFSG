module

public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup

/-!
# Self-centralizing root planes in the binary linear group

The point and line radicals consist of four explicit upper unitriangular
matrices. Finite coordinate calculations identify their normalizers with the
flag parabolics and show that each radical is self-centralizing in SL₃(2).
A normal two-subgroup lies in the intrinsic two-core, giving the required
centralizer bound in each parabolic.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed p.4, and the binary plane model in I.5.3–4,
printed pp.419–420. All finite calculations are checked by the Lean kernel.
-/

open Matrix Matrix.PSL3Two

namespace CFSG.Quasithin.MainConverse.BinaryThree

private abbrev V := Multiplicative (Fin 2 → ZMod 2)

private def rootMatrix (side : Bool) (v : V) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if side then !![1, v.toAdd 0, v.toAdd 1; 0, 1, 0; 0, 0, 1]
  else !![1, 0, v.toAdd 0; 0, 1, v.toAdd 1; 0, 0, 1]

private theorem rootMatrix_det : ∀ side v, (rootMatrix side v).det = 1 := by decide

private def rootElement (side : Bool) (v : V) : SL :=
  ⟨rootMatrix side v, rootMatrix_det side v⟩

private theorem rootElement_one : ∀ side, rootElement side 1 = 1 := by decide
private theorem rootElement_mul : ∀ side v w,
    rootElement side (v * w) = rootElement side v * rootElement side w := by decide

private def rootHom (side : Bool) : V →* SL where
  toFun := rootElement side
  map_one' := rootElement_one side
  map_mul' := rootElement_mul side

private def radical (side : Bool) : Subgroup SL := (rootHom side).range

private instance (side : Bool) : DecidablePred (· ∈ radical side) :=
  fun g => inferInstanceAs (Decidable (∃ v, rootHom side v = g))

private def parabolic (side : Bool) : Subgroup SL :=
  if side then pointParabolicSL else lineParabolicSL

private instance (side : Bool) : DecidablePred (· ∈ parabolic side) := by
  cases side <;> dsimp [parabolic] <;> infer_instance

private theorem radical_le : ∀ side, radical side ≤ parabolic side := by
  intro side g hg
  obtain ⟨v, rfl⟩ := hg
  have h : ∀ side v, rootHom side v ∈ parabolic side := by decide
  exact h side v

private theorem radical_two : ∀ side, IsPGroup 2 (radical side) := by
  intro side
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  obtain ⟨v, hv⟩ := x.property
  change (x : SL) ^ 2 = 1
  rw [← hv, ← map_pow]
  have hv2 : ∀ v : V, v ^ 2 = 1 := by decide
  rw [hv2, map_one]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem radical_normalizer : ∀ side g,
    (∀ v : V, g * rootHom side v * g⁻¹ ∈ radical side) ↔ g ∈ parabolic side := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem radical_centralizer : ∀ side g,
    (∀ v : V, rootHom side v * g = g * rootHom side v) → g ∈ radical side := by
  decide +kernel

private theorem radical_ne_bot (side : Bool) : radical side ≠ ⊥ := by
  intro h
  have hmem : rootHom side (Multiplicative.ofAdd ![1, 0]) ∈ radical side :=
    ⟨_, rfl⟩
  have heq : rootHom side (Multiplicative.ofAdd ![1, 0]) = 1 := by
    simpa only [h, Subgroup.mem_bot] using hmem
  have hne : ∀ side, rootHom side (Multiplicative.ofAdd ![1, 0]) ≠ 1 := by decide
  exact hne side heq

private theorem normalizer_radical (side : Bool) :
    Subgroup.normalizer (radical side : Set SL) = parabolic side := by
  apply le_antisymm
  · intro g hg
    apply (radical_normalizer side g).mp
    intro v
    exact (hg (rootHom side v)).mp ⟨v, rfl⟩
  · rw [Subgroup.le_set_normalizer_iff]
    intro g hg x hx
    obtain ⟨v, rfl⟩ := hx
    exact (radical_normalizer side g).mpr hg v

private theorem parabolic_twoLocal (side : Bool) : IsTwoLocal (parabolic side) :=
  ⟨radical side, radical_ne_bot side, radical_two side, (normalizer_radical side).symm⟩

private theorem parabolic_characteristicTwo (side : Bool) :
    HasCharacteristicTwo (parabolic side) := by
  apply centralizer_pCore_le_of_normalized 2 (radical side) (parabolic side)
    (radical_two side) (radical_le side) (normalizer_radical side ▸ le_rfl)
  intro g hg
  apply radical_centralizer side g
  intro v
  exact (Subgroup.mem_centralizer_iff.mp hg) (rootHom side v) ⟨v, rfl⟩

public theorem pointParabolicSL_twoLocal : IsTwoLocal pointParabolicSL :=
  parabolic_twoLocal true

public theorem lineParabolicSL_twoLocal : IsTwoLocal lineParabolicSL :=
  parabolic_twoLocal false

public theorem pointParabolicSL_characteristicTwo : HasCharacteristicTwo pointParabolicSL :=
  parabolic_characteristicTwo true

public theorem lineParabolicSL_characteristicTwo : HasCharacteristicTwo lineParabolicSL :=
  parabolic_characteristicTwo false

end CFSG.Quasithin.MainConverse.BinaryThree
