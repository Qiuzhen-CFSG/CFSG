module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.Centers
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure

/-!
# Centerlessness of the two full Ree parabolics

Characteristic two puts a parabolic-central element in its two-core and hence
in the positive Sylow subgroup. The positive-center calculation places it on
the long-root curve. Every nonzero point of that curve is conjugate under the
whole Borel; the field has more than two elements, so none can be central in
the full parabolic. This works for every positive parameter, including q=8.

The original full-normalizer action uses this result to kill its kernel after
characteristic two puts that kernel inside the parabolic. It does not extend
local automorphisms to the whole Ree group.
Source: Aschbacher–Smith 5.3.1–2 and F.4.3, printed pp.658–659,274;
GLS3 Table 2.4, using the existing root-center and Borel-orbit calculations.
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Theory.GroupTheory Parabolics LargeLocalSeeds EvenInvolutionGeometry

/-- Both full parabolics are centerless at every positive Ree parameter. -/
theorem parabolic_center_eq_bot {m : ℕ} (hm : 0 < m) (s : Side) :
    center (parabolic m s) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have hcore := ConverseParabolics.parabolic_centralizer_pCore_le hm s
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hcore
  have hzQ : z ∈ pCore 2 (parabolic m s) :=
    hcore (center_le_centralizer (pCore 2 (parabolic m s) : Set (parabolic m s)) hz)
  have hindex : Odd (unipotent m).index :=
    OuterLocal.LargeAutomorphisms.unipotent_index_odd_of_standard (canonicalLocalBlockInput m)
      (FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m))
  let U := (sylowOfOddIndex m hindex).subtype ((unipotent_le_localFactor m s).trans (localFactor_le_parabolic m s))
  have hzU : z.val ∈ unipotent m := pCore_isPGroup.le_sylow_of_normal U hzQ
  have hc : ∀ u ∈ unipotent m, Commute z.val u := by
    intro u hu
    exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨u,(unipotent_le_localFactor m s).trans (localFactor_le_parabolic m s) hu⟩)).symm
  obtain ⟨t,ht⟩ := eq_longRootElement_of_central_unipotent m hm z.val hzU hc
  have hroot : z.val ∈ longRootGroup m := (mem_longRootGroup m _).mpr ⟨t,ht.symm⟩
  by_cases hz1 : z.val = 1
  · exact mem_bot.mpr (Subtype.ext hz1)
  have hq : 2 < Nat.card (CoefficientField m) := by
    rw [field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2^3)
      (Nat.pow_le_pow_right (by decide) (by omega))
  let : Nontrivial (CoefficientField m)ˣ := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [Nat.card_units]
    omega
  obtain ⟨u,hu⟩ := exists_ne (1 : (CoefficientField m)ˣ)
  have he (a : CoefficientField m) (ha : a ≠ 0) : longRootElement m a = z.val := by
    obtain ⟨g,hg,he⟩ := longRoot_borel_orbit m z.val (longRootElement m a)
      hroot ((mem_longRootGroup m _).mpr ⟨a,rfl⟩) hz1
      ((longRootElement_eq_one_iff m a).not.mpr ha)
    have hcomm := congrArg Subtype.val (mem_center_iff.mp hz
      ⟨g,borel_le_parabolic m s hg⟩)
    change g * z.val = z.val * g at hcomm
    rw [he,hcomm,mul_inv_cancel_right]
  have heu := longRootElement_injective m ((he u u.ne_zero).trans (he 1 one_ne_zero).symm)
  exact (hu (Units.ext heu)).elim
end ReeF4.SourceCompletion
