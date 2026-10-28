module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation.PrimeOrder
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.Basic

/-!
# Fitting-commutator generation in the quasisimple FF branch

The Fitting subgroup centralizes the quasisimple generalized Fitting
subgroup and lies in it, hence embeds in its center. Each of the ten actual
model identifications makes this center have order dividing three. This
includes the triple cover and all even SL₃ fields; neither centrality in
the whole actor nor a centerless model is assumed. The prime-order normal
closure argument now applies to the actual Thompson star image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(1), printed p.105; paragraph after 13.6.13, printed p.929.
Model computations retain the attribution of their imported ATLAS ports.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
variable {D : Type*} [Group D] [Finite D]

private theorem g2_center (F : Type*) [Field F] [Finite F] [IsQuasisimple (Atlas.G2.Model F)] :
    center (Atlas.G2.Model F) = ⊥ := by
  have hlarge : 2 < Nat.card F := by
    have hpos := Finite.one_lt_card (α := F)
    by_contra h
    have htwo : Nat.card F = 2 := by omega
    let e := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv htwo)
    let := IsQuasisimple.of_mulEquiv e
    have he := Group.IsPerfect.commutator_eq_top (G := Atlas.G2.Model (ZMod 2))
    have hc := congrArg (fun S : Subgroup (Atlas.G2.Model (ZMod 2)) => Nat.card S) he
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure] at hc
    rw [Atlas.G2.BinaryException.card_H, Nat.card_congr Subgroup.topEquiv.toEquiv,
      Atlas.G2.card_Model] at hc
    norm_num only [Nat.card_zmod, Nat.reducePow, Nat.reduceMul, Nat.reduceSub,
      Nat.reduceEqDiff] at hc
  let := Atlas.G2.isSimple hlarge
  rcases (inferInstance : (center (Atlas.G2.Model F)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let : IsSimpleGroup (Atlas.G2.Model F ⧸ center (Atlas.G2.Model F)) := IsQuasisimple.simple
    let : Nontrivial (Atlas.G2.Model F) := (QuotientGroup.mk'_surjective (center _)).nontrivial
    exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim

omit [Finite D] in
theorem quasisimple_center_card [IsQuasisimple D] (h : QuasisimpleModel D) :
    Nat.card (center D) ∣ 3 := by
  cases h with
  | linearTwo F e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot, card_bot]
    exact one_dvd _
  | linearThree F e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center]
    exact Nat.gcd_dvd_left _ _
  | symplecticFour F e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot, card_bot]
    exact one_dvd _
  | g2 F e =>
    let := IsQuasisimple.of_mulEquiv e
    rw [Nat.card_congr (centerCongr e).toEquiv, g2_center, card_bot]
    exact one_dvd _
  | alternatingSix e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by simp), card_bot]
    exact one_dvd _
  | alternatingSeven e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by simp), card_bot]
    exact one_dvd _
  | tripleSix e _ =>
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (ZMod 3) ∣ 3
    rw [Nat.card_zmod]
  | g2DerivedTwo e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Theory.SpecificGroups.g2_derived_two_center_eq_bot, card_bot]
    exact one_dvd _
  | linearFourTwo e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center]
    norm_num
  | linearFiveTwo e =>
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center]
    norm_num

theorem fitting_le_center_generalized [IsQuasisimple (generalizedFitting D)] :
    fittingSubgroup D ≤ (center (generalizedFitting D)).map (generalizedFitting D).subtype := by
  have hL : IsComponent D (generalizedFitting D) :=
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, inferInstance⟩
  have hc := le_centralizer_iff.mp
    (component_centralizes_of_le_normalizer _ (fittingSubgroup D) hL
      (by rw [normalizer_eq_top]; exact le_top))
  intro x hx
  refine ⟨⟨x, fitting_le_generalizedFitting D hx⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_centralizer_iff.mp (hc hx) y y.property)

theorem quasisimple_fitting_card [IsQuasisimple (generalizedFitting D)]
    (h : QuasisimpleModel (generalizedFitting D)) : Nat.card (fittingSubgroup D) ∣ 3 := by
  have hd := card_dvd_of_le (fitting_le_center_generalized (D := D))
  rw [card_map_of_injective (generalizedFitting D).subtype_injective] at hd
  exact hd.trans (quasisimple_center_card h)

variable {G : Type*} [Group G] [Finite G]

/-- The quasisimple source branch on the actual Thompson action. -/
theorem thompson_generation_of_quasisimple
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hq : IsQuasisimple (generalizedFitting (JGstar z v)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion (thompsonRepresentation z v hz)
      (generalizedFitting (JGstar z v))) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) := by
  let := hq
  exact thompson_generation_of_fitting_card_dvd_prime T z v hSyl (by decide : Nat.Prime 3)
    (quasisimple_fitting_card (c.fittingModel _))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
