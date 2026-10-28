module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Extension.Setup
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Extension.Model
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelFacts.Residual
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension

/-!
# Extending the marked centralizer from its A₅ residual

The literal local map sends K ∩ L into C_A₉(t9). Transfer identifies its
intersection with O²(K); the concrete model geometry identifies the same
intersection on the target. A₅ marking extension gives an equivalence
between the residuals. Faithfulness of restriction to their A₄ subgroup
forces the conjugation actions to match, so normal-supplement gluing gives
an equivalence on all of K which retains the prescribed local map.

The final comparison theorem supplies the distinguished-element equation
and both ambient fusion fields. The proved eight-point residual order
discharges the local cardinality premise of the nine-point model, and the
A₅ marking and restriction theorems discharge the gluing premises. Thus the
final results require only residual recognition and transfer, in addition
to the original marked local data and centralizer containment. The parent
second-centralizer assembly supplies those two residual inputs.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
namespace Extension
variable {G : Type*} [Group G] [Finite G] {z : G} {L : Subgroup G}

private theorem localResidual_mem (d : InvolutionData z L) (a : d.M) :
    localModelEquiv d a ∈ modelLocalResidual ↔ a ∈ pResidual 2 d.M := by
  have h := map_pResidual_of_surjective 2 (localModelEquiv d).toMonoidHom
    (localModelEquiv d).surjective
  change localModelEquiv d a ∈ pResidual 2 (Centralizer t8) ↔ _
  rw [← h]
  constructor
  · rintro ⟨b, hb, he⟩
    exact (localModelEquiv d).injective he ▸ hb
  · intro ha
    exact mem_map.mpr ⟨a, ha, rfl⟩

private theorem local_mem_residual (d : InvolutionData z L)
    (htransfer : d.J ⊓ L = d.X) (a : d.M) :
    a.val ∈ pResidual 2 d.K ↔ a ∈ pResidual 2 d.M := by
  have h := residual_inf_local d htransfer
  constructor
  · intro ha
    obtain ⟨b, hb, he⟩ := mem_map.mp (h ▸ (show a.val ∈ pResidual 2 d.K ⊓ d.M from
      ⟨ha, a.property⟩))
    exact d.M.subtype_injective he ▸ hb
  · intro ha
    exact ((h.symm ▸ mem_map.mpr ⟨a, ha, rfl⟩) : a.val ∈ pResidual 2 d.K ⊓ d.M).1

private theorem intersection_card (d : InvolutionData z L)
    (htransfer : d.J ⊓ L = d.X) (geom : ModelGeometry) :
    Nat.card (d.M.subgroupOf (pResidual 2 d.K)) = 12 := by
  let N := pResidual 2 d.K
  let S := d.M.subgroupOf N
  have hS : S.map N.subtype = (pResidual 2 d.M).map d.M.subtype := by
    rw [subgroupOf_map_subtype, inf_comm]
    exact residual_inf_local d htransfer
  let eS := (S.equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr hS)
  let eM := (pResidual 2 d.M).equivMapOfInjective d.M.subtype d.M.subtype_injective
  let eR := ((pResidual 2 d.M).equivMapOfInjective (localModelEquiv d).toMonoidHom
    (localModelEquiv d).injective).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 (localModelEquiv d).toMonoidHom
      (localModelEquiv d).surjective))
  exact (Nat.card_congr (eS.trans (eM.symm.trans eR)).toEquiv).trans geom.local_card

/-- Once the concrete model and A₅ restriction theorems are supplied,
residual recognition and transfer produce the required literal extension. -/
public theorem centralizerExtension_of_model_and_marking (d : InvolutionData z L)
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) (eJ : d.J ≃* alternatingGroup (Fin 5))
    (geom : ModelGeometry)
    (hm : AlternatingFiveSubgroupExtension.MarkingExtension)
    (hr : AlternatingFiveSubgroupExtension.RestrictionFaithful) :
    Nonempty (CentralizerExtension d) := by
  have hinter (m : d.M) : localEmbedding d m ∈ modelResidual ↔
      (m : d.K) ∈ pResidual 2 d.K := by
    change localModelEquiv d m ∈ modelResidual.comap modelLocalEmbedding ↔ _
    rw [geom.local_intersection, localResidual_mem, local_mem_residual d htransfer]
  have hgen : modelResidual ⊔ (localEmbedding d).range = ⊤ := by
    have he : (localEmbedding d).range = modelLocalEmbedding.range := by
      apply le_antisymm
      · rintro x ⟨m, rfl⟩
        exact ⟨localModelEquiv d m, rfl⟩
      · rintro x ⟨m, rfl⟩
        obtain ⟨a, rfl⟩ := (localModelEquiv d).surjective m
        exact ⟨a, rfl⟩
    rw [he, geom.generation]
  obtain ⟨E, hE⟩ := AlternatingFiveSubgroupExtension.exists_equiv_normal_supplement hm hr
    (pResidual 2 d.K) d.M modelResidual ((residualEquiv d).trans eJ)
    geom.residual_equiv (localEmbedding d) (localEmbedding_injective d)
    (residual_sup_local d hz hCL) hgen hinter (intersection_card d htransfer geom)
  refine ⟨⟨E, ?_⟩⟩
  intro a ha
  exact (congrArg (fun x : Centralizer t9 => (x : Nine)) (hE ⟨a, ha⟩)).trans
    (localEmbedding_coe d ⟨a, ha⟩)

/-- The existing fusion comparison applies to the constructed extension.
This intermediate version retains the concrete model and A₅ subgroup
obligations, discharged in `secondCentralizerData_of_residual` below. -/
public theorem secondCentralizerData_of_model_and_marking (d : InvolutionData z L)
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) (eJ : d.J ≃* alternatingGroup (Fin 5))
    (geom : ModelGeometry)
    (hm : AlternatingFiveSubgroupExtension.MarkingExtension)
    (hr : AlternatingFiveSubgroupExtension.RestrictionFaithful) :
    Nonempty (SecondCentralizerData d) := by
  obtain ⟨c⟩ := centralizerExtension_of_model_and_marking d hz hCL htransfer eJ geom hm hr
  exact ⟨c.secondCentralizerData hz hCL⟩

/-- Extend the recognized residual while retaining the prescribed eight-point
map on every element of K ∩ L. The concrete residual geometry and A₅ marking
premises are discharged; only the source's residual recognition and transfer
remain as explicit inputs. -/
public theorem centralizerExtension_of_residual (d : InvolutionData z L)
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) (eJ : d.J ≃* alternatingGroup (Fin 5)) :
    Nonempty (CentralizerExtension d) := by
  have h12 : Nat.card modelLocalResidual = 12 :=
    (Nat.card_congr ((pResidual 2 ResidualModel.C).equivMapOfInjective
      ResidualModel.C.subtype ResidualModel.C.subtype_injective).toEquiv).trans
      ResidualModel.R_card
  obtain ⟨geom⟩ := modelGeometry_nonempty h12
  exact centralizerExtension_of_model_and_marking d hz hCL htransfer eJ geom
    AlternatingFiveSubgroupExtension.markingExtension
    AlternatingFiveSubgroupExtension.restrictionFaithful

/-- The literal extension supplies the distinguished t-image and both ambient
fusion fields on all of K, with the same explicit residual inputs. -/
public theorem secondCentralizerData_of_residual (d : InvolutionData z L)
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) (eJ : d.J ≃* alternatingGroup (Fin 5)) :
    Nonempty (SecondCentralizerData d) := by
  obtain ⟨c⟩ := centralizerExtension_of_residual d hz hCL htransfer eJ
  exact ⟨c.secondCentralizerData hz hCL⟩

end Extension
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
