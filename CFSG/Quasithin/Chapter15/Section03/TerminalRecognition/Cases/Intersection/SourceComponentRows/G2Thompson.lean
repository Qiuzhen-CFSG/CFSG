module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows.G2Action

/-!
# The literal Thompson image in the corrected G₂(2) row

A maximum elementary subgroup of H gives an offender on the original
quotient action and then on the selected central section. The marked
rank-three clause forces its image outside G₂(2)′. The component
containment and index two now give the full Thompson image.

The proofs adapt the existing terminal `ComponentRows` comparison to the
full `ProjectiveLine.QuasisimpleSourceConclusion`. The two-dimensional
F₄ offender clause remains on the original action; no legacy clause is
constructed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1/B.5.6,
printed pp.99–105; F.6.18, pp.309–310; K.1.3, p.453; final proof of
15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem derived_elementary_card
    (A : Subgroup (commutator (Atlas.G2.Model (ZMod 2))))
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let e := S.equiv Atlas.G2.BinaryParabolicPair.derivedSylow
  let B := A.subgroupOf (S : Subgroup (commutator (Atlas.G2.Model (ZMod 2))))
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAS
  let _ : IsElementaryAbelian 2 (B.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hb := ABG.elementary_card_le_four_of_isWreathedOfHeight
    Atlas.G2.BinaryParabolicPair.derivedSylow_isWreathedOfHeight (B.map e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective] at hb
  exact (Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv).symm.le.trans hb

private theorem offender_subgroupOf {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {A I : Subgroup D} (hA : IsOffender ρ A) (hAI : A ≤ I) :
    IsOffender (ρ.comp I.subtype) (A.subgroupOf I) := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have hm := map_subgroupOf_eq_of_le hAI
  refine ⟨⟨?_, IsElementaryAbelian.subgroupOf hAI⟩, ?_⟩
  · intro hb
    apply hA.1.1
    rw [← hm, hb, Subgroup.map_bot]
  · have hr := rank_map_injective I.subtype I.subtype_injective (A.subgroupOf I)
    rw [hm] at hr
    change fixedCodim (ρ.comp I.subtype) (A.subgroupOf I) ≤ _
    unfold fixedCodim
    rw [fixedSpace_comp_map, hm, ← hr]
    exact hA.2

private theorem movedSection_offender {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L : Subgroup D} (s : MovedSection ρ L)
    {A : Subgroup D} (hA : IsOffender ρ A) : IsOffender s.action A := by
  refine ⟨hA.1, ?_⟩
  have hq := fixedCodim_quotient_add_subrepresentation_le
    s.space.toRepresentation s.central A
  have hs := fixedCodim_subrepresentation_le ρ s.space A
  change fixedCodim s.action A + _ ≤ _ at hq
  exact (Nat.le_add_right _ _).trans (hq.trans (hs.trans hA.2))

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

private theorem source_maxElementary_image_rank_g2
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (eL : generalizedFitting (coreQuotient H) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (A : Subgroup H) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤)
    (hne : ¬ A ≤ (coreProjection (H := H)).ker) :
    rank (A.map coreProjection) = 3 := by
  let ρ := quotientAction V d.centralizer_isTwoGroup d.core_centralizes
  have ho : IsOffender ρ (A.map coreProjection) :=
    Representation.NormalElementaryQuotient.maxElementary_isOffender
      (moduleClosure V) coreProjection (QuotientGroup.mk'_surjective _)
      (coreProjection_ker V d.centralizer_isTwoGroup d.core_centralizes) ⊤ A le_top hA hne
  have hAI : A.map coreProjection ≤ d.offenderGroup :=
    (map_mono (show A ≤ thompsonGroup H from le_sSup hA)).trans d.thompson_image_le_offender
  have hb : IsOffender d.offenderAction ((A.map coreProjection).subgroupOf d.offenderGroup) :=
    offender_subgroupOf ρ ho hAI
  have hc : Nat.card (generalizedFitting d.offenderGroup) = 6048 := by
    rw [Nat.card_congr ((d.offenderFittingEquiv hL).trans eL).toEquiv,
      Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H]
  obtain ⟨_, _, hr, hq⟩ := SourceComponentRows.G2.projectiveLine_source_g2_marked d.offenderAction c hc
  have hs := movedSection_offender d.offenderAction c.sectionData hb
  have hrank := hr _ (hs.best_and_codim_eq_of_quadraticRatio_eq_one _ hq).1
  have he := rank_map_injective d.offenderGroup.subtype d.offenderGroup.subtype_injective
    ((A.map coreProjection).subgroupOf d.offenderGroup)
  rwa [map_subgroupOf_eq_of_le hAI, hrank] at he

/-- In the terminal G₂(2) row, the image of the original Thompson subgroup
is the whole original core quotient. -/
theorem source_thompson_image_eq_top_of_g2
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (eD : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (eL : generalizedFitting (coreQuotient H) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (thompsonGroup H).map coreProjection = ⊤ := by
  classical
  let X := (thompsonGroup H).map coreProjection
  let L := generalizedFitting (coreQuotient H)
  have hLX : L ≤ X := d.fitting_le_thompson hL
  have hLc : Nat.card L = 6048 := by
    rw [Nat.card_congr eL.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H]
  have hDc : Nat.card (coreQuotient H) = 12096 := by
    rw [Nat.card_congr eD.toEquiv, Atlas.G2.card_Model]
    norm_num
  have hLi : L.index = 2 := by
    have hh := L.card_mul_index
    rw [hLc, hDc] at hh
    omega
  have hXi : X.index ∣ 2 := by
    simpa only [hLi] using index_dvd_of_le hLX
  rcases (Nat.dvd_prime Nat.prime_two).mp hXi with hi | hi
  · exact index_eq_one.mp hi
  have hXL : X ≤ L := by
    apply relIndex_eq_one.mp
    have hh := relIndex_mul_index hLX
    rw [hi, hLi] at hh
    omega
  have hex : ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup H),
      ¬ A ≤ (coreProjection (H := H)).ker := by
    by_contra! hh
    exact d.thompson_image_ne_bot ((Subgroup.map_eq_bot_iff _).mpr (sSup_le hh))
  obtain ⟨A, hA, hne⟩ := hex
  let B := A.map coreProjection
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBL : B ≤ L := (map_mono (show A ≤ thompsonGroup H from le_sSup hA)).trans hXL
  let _ : IsElementaryAbelian 2 (B.subgroupOf L) := IsElementaryAbelian.subgroupOf hBL
  let _ : IsElementaryAbelian 2 ((B.subgroupOf L).map eL.toMonoidHom) :=
    IsElementaryAbelian.map _
  have hb := derived_elementary_card ((B.subgroupOf L).map eL.toMonoidHom)
  rw [Subgroup.card_map_of_injective eL.injective,
    Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv] at hb
  have hr : rank B = 3 := d.source_maxElementary_image_rank_g2 hL c eL A hA hne
  have hc : Nat.card B = 8 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    rw [rank, hn, Nat.log_pow (by decide : 1 < 2)] at hr
    simpa [hr] using hn
  omega

/-- The required full G₂(2) model for the literal image of J(H). -/
theorem source_thompson_image_g2
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (eD : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (eL : generalizedFitting (coreQuotient H) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Atlas.G2.Model (ZMod 2)) :=
  ⟨(MulEquiv.subgroupCongr (d.source_thompson_image_eq_top_of_g2 hL c eD eL)).trans
    (topEquiv.trans eD)⟩

end SourceInput

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
