module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.Reduction
public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Connecting G₂ placement to the intrinsic component Borel

Sylow conjugacy aligns a solvable overgroup with the six positive root
groups. Once it lies in a full root parabolic, the checked rank-one
calculation makes it normalize that Sylow subgroup. Transport back retains
the original Sylow marking. The concrete Bruhat calculation supplies standard
placement, and the actual model equivalence transports the conclusion to the
field-marked component, including the field of four elements.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the first
paragraph of the final proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel

/-- The independent standard-placement theorem suffices; arbitrary Sylow
transport and the full-parabolic refinement are discharged here. -/
theorem g2_control_of_standard_placement
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hq : 2 < Nat.card F)
    (hplace : ∀ H : Subgroup (Model F), unipotent ≤ H → Group.IsSolvable H →
      H ≤ parabolic₁ ∨ H ≤ parabolic₂) : ParabolicSolvableControl (Model F) := by
  intro U P H _hNP _hP _hHP hsol hUH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) U (sylow (F := F))
  let a := MulAut.conj g
  have hU : (U : Subgroup (Model F)).map a.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable H := hsol
  have hsol' : Group.IsSolvable (H.map a.toMonoidHom) :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective H)
  have hUH' : unipotent ≤ H.map a.toMonoidHom := by
    rw [← hU]
    exact map_mono hUH
  have hN := SolvableParabolic.normalizes hq sylow _ hUH' hsol'
    (hplace _ hUH' hsol')
  change H.map a.toMonoidHom ≤ normalizer (unipotent (K := F) : Set (Model F)) at hN
  rw [← hU, ← map_equiv_normalizer_eq] at hN
  exact (map_le_map_iff_of_injective a.injective).mp hN

/-- The larger-field G₂ control, with standard placement proved in the full
split-octonion model and transported through the given model equivalence. -/
theorem g2_control {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : 1 < n) (hmodel : ClassificationModels.IsG2At D (2 ^ n)) :
    ParabolicSolvableControl D := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  exact control_of_mulEquiv e (g2_control_of_standard_placement hq
    (fun H hU hH => SolvableSylowPlacement.le_parabolic hq H hU hH))

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel
