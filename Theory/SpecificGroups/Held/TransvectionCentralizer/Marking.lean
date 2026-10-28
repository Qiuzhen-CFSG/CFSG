module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities
public import Theory.SpecificGroups.Held.TransvectionCentralizer.CentralizerBound
public import Theory.SpecificGroups.Held.TransvectionCentralizer.SylowComplement
public import Theory.SpecificGroups.BinaryLinear.AffineFourSplitMarking
public import Theory.GroupTheory.Recognition.TransvectionFive.Marking
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.ElementarySixteenComplement
import all Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.ElementarySixteenComplement

/-! The literal row-nine subgroup and its certified Sylow complement give
an actual marking of the full native Held 2B centralizer. -/

public noncomputable section
namespace Held.TransvectionCentralizer
open Subgroup LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates TwoLocalCandidates.MaximalNormalizerCatalogue
open Theory.GroupTheory
open scoped IsMulCommutative

private theorem centralizer_eq_overgroup :
    centralizer ({centralWord} : Set He) =
      E64Containment.CentralizerCertificates.UpperBounds.overgroup := by
  have h := AutomorphismLocalPair.representative_centerLocal
  rw [AutomorphismLocalPair.centerLocal, AutomorphismLocalPair.representative_centerSeed,
    zpowers_eq_closure, centralizer_closure] at h
  exact h

public theorem centralizer_card : Nat.card (centralizer ({centralWord} : Set He)) = 21504 := by
  rw [centralizer_eq_overgroup]
  exact E64Containment.CentralizerCertificates.UpperBounds.overgroup_card

public theorem row_nine_elementary : IsElementaryAbelian 2 (ambient 9) := by
  let := SylowComplement.row_nine_elementary
  exact IsElementaryAbelian.map representative.subtype

public theorem row_nine_card : Nat.card (ambient 9) = 16 := by
  rw [ambient, card_map_of_injective representative.subtype_injective]
  exact SylowComplement.row_nine_card

set_option maxRecDepth 4096 in
public theorem row_nine_normalizer :
    normalizer (ambient 9 : Set He) = centralizer ({centralWord} : Set He) := by
  apply eq_of_le_of_card_ge (rankFour_normalizer_le_centralizer 1 (by decide))
  have hc : Nat.card ((subgroup (candidate 1)).map
      (MulAut.conj (conjugator 1)).toMonoidHom) = Nat.card (subgroup (candidate 1)) :=
    card_map_of_injective (K := subgroup (candidate 1))
      (f := (MulAut.conj (conjugator 1)).toMonoidHom) (MulAut.conj (conjugator 1)).injective
  calc
    Nat.card (centralizer ({centralWord} : Set He)) = 21504 := centralizer_card
    _ = Nat.card (subgroup (candidate 1)) := InvolutionFixedData.TwoB.max5_card.symm
    _ = Nat.card ((subgroup (candidate 1)).map
        (MulAut.conj (conjugator 1)).toMonoidHom) := hc.symm
    _ ≤ Nat.card (normalizer (ambient 9 : Set He)) :=
      Nat.card_le_card_of_injective (inclusion (conjugated_candidate_le_normalizer 1))
        (inclusion_injective (conjugated_candidate_le_normalizer 1))

public theorem row_nine_selfcentralizing : centralizer (ambient 9 : Set He) = ambient 9 := by
  let := row_nine_elementary
  apply (eq_of_le_of_card_ge (le_centralizer_iff_isMulCommutative.mpr inferInstance) ?_).symm
  rw [row_nine_card]
  exact CentralizerBound.centralizer_card_le representative_isPGroup

/-- The whole actual involution centralizer, with its supplied point and
literal elementary-sixteen column, has the marked transvection shape. -/
theorem exists_marking : ∃ F : TransvectionFive.MarkedCentralizer centralWord,
    ambient 9 = F.column := by
  let A := ambient 9
  let C := centralizer ({centralWord} : Set He)
  have hz : centralWord ≠ 1 := by
    intro h
    have hh := centralWord_order
    simp [h] at hh
  have hzA : centralWord ∈ A :=
    E64Containment.CentralizerCertificates.centralWord_mem_ambient 9
  let := row_nine_elementary
  have hAT : A ≤ (AutomorphismLocalPair.representativeSylow : Subgroup He) := by
    rw [AutomorphismLocalPair.representativeSylow_coe]
    exact ambient_le_representative 9
  have hTC : (AutomorphismLocalPair.representativeSylow : Subgroup He) ≤ C := by
    rw [AutomorphismLocalPair.representativeSylow_coe]
    exact representative_le_centralizer_centralWord
  let S := AutomorphismLocalPair.representativeSylow.subtype hTC
  let e : S ≃* representative := (subgroupOfEquivOfLe hTC).trans
    (MulEquiv.subgroupCongr AutomorphismLocalPair.representativeSylow_coe)
  have heA : (A.subgroupOf C).subgroupOf S = (entry 9).comap e.toMonoidHom := by
    ext x
    change (x.val.val : He) ∈ (entry 9).map representative.subtype ↔ e x ∈ entry 9
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, he⟩
      have hey : y = e x := Subtype.ext he
      exact hey ▸ hy
    · intro hx
      exact ⟨e x, hx, rfl⟩
  obtain ⟨L, hL⟩ := SylowComplement.exists_complement
  have hs : ∃ L' : Subgroup S, ((A.subgroupOf C).subgroupOf S).IsComplement' L' := by
    refine ⟨L.comap e.toMonoidHom, ?_⟩
    rw [heA]
    exact Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.ElementarySixteenComplement.complement_comap
      e (entry 9) L hL
  obtain ⟨M⟩ := BinaryLinear.Affine.exists_pointMarking_of_sylow_split_sixteen
    centralWord hz A hzA row_nine_card (hAT.trans hTC) row_nine_normalizer.symm.le
    (by rw [row_nine_selfcentralizing]; exact inf_le_right) centralizer_card S hs
  exact ⟨TransvectionFive.markingOfAffine M hz, TransvectionFive.markingOfAffine_column M hz⟩

end Held.TransvectionCentralizer
