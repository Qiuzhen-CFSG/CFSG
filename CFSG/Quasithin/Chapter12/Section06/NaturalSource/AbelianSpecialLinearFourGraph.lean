module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourOuter
public import Theory.SpecificGroups.PSL3Four.OuterGraphSelection
public import Theory.Representation.SL3FourNaturalDual
/-!
# A graph actor in the original Sylow subgroup

The literal quotient H-star/K-star is E₄. Its faithful outer action fills
the field–graph quotient, so a graph class lifts to the original T-star.
Perfect central descent gives its explicit GL₃-corrected inverse-transpose
action on the full SL₃(4), including the scalar center. The lift back to T
uses the original quotient projection, and the last theorem constructs the
field marking from K/O₂(K) without replacing the selected component.

The conjugation equation is oriented exactly as required by the natural and
dual module arguments. Earlier geometry remains explicit.
Source: Aschbacher–Smith 12.6.31(1) and 12.6.32, printed p.837.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)

open Matrix.PSL3.OuterSolvable
local notation "F₄" => Representation.SL3FourNaturalDual.F

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- An actual element of the original T has a graph action on the full component. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_graph
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)
    (hn : (K.subgroupOf H).Normal)
    (e : actorImage H K ≃* SL(3,F₄)) :
    letI : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
    let ι : T →* H := inclusion (fun _x hx => hH.1.2 (Or.inr hx))
    ∃ t : T, ∃ c : Matrix.GeneralLinearGroup (Fin 3) F₄,
      MulAut.congr e (MulAut.conjNormal (((QuotientGroup.mk' (pCore 2 H)) (ι t))⁻¹)) =
        linearConjSL F₄ c * graphSL F₄ := by
  let B := actorImage H K
  let π := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  have hTH : (T : Subgroup G) ≤ H := fun _x hx => hH.1.2 (Or.inr hx)
  have hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 :=
    ⟨F₄,inferInstance,inferInstance,(by rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]),
      ⟨(componentStarEquiv H K hKH hK).trans e⟩⟩
  let _ := S.original_abelian_normal_specialLinearFour_kleinFour
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  have hq : IsQuasisimple B :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  let _ := hq
  obtain ⟨_,_,hfit⟩ := S.original_abelian_normal_specialLinearFour_quotient
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  have hc : centralizer (B : Set (H ⧸ pCore 2 H)) ≤ B := by
    change centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) ≤ actorImage H K
    rw [←hfit]
    exact centralizer_generalizedFitting_le (H ⧸ pCore 2 H)
  obtain ⟨_,hg⟩ := S.original_abelian_normal_specialLinearFour_reduction
    D hZ z hz hTV hTz hbound hTI hns hH hKH hgen hn hm
  have hsup : B ⊔ actorImage H T = ⊤ := by
    unfold B actorImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hKH hTH,hg,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨a,c,ha⟩ := Matrix.PSL3Four.OuterGraphSelection.exists_full_graph_of_normal_supplement
    (by rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]) B (actorImage H T) e hc hsup
  obtain ⟨t,ht,he⟩ := a.property
  let t₀ : T := ⟨(t : G),ht⟩
  refine ⟨t₀⁻¹,c,?_⟩
  have heq : π (inclusion hTH t₀) = a.val := he
  have hts : (π (inclusion hTH t₀⁻¹))⁻¹ = a.val := by
    rw [map_inv,map_inv,inv_inv,heq]
  change MulAut.congr e (MulAut.conjNormal ((π (inclusion hTH t₀⁻¹))⁻¹)) = _
  rw [hts]
  exact ha

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The literal quotient action has the inverse-conjugation convention of the module API. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_graph_relation
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)
    (hn : (K.subgroupOf H).Normal)
    (e : actorImage H K ≃* SL(3,F₄)) :
    let ι : T →* H := inclusion (fun _x hx => hH.1.2 (Or.inr hx))
    ∃ t : T, ∃ c : Matrix.GeneralLinearGroup (Fin 3) F₄,
      ∀ g : SL(3,F₄),
        (e.symm g).val * (QuotientGroup.mk' (pCore 2 H)) (ι t) =
          (QuotientGroup.mk' (pCore 2 H)) (ι t) *
            (e.symm (linearConjSL F₄ c (Matrix.SpecialLinearGroup.inverseTranspose g))).val := by
  let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  let ι : T →* H := inclusion (fun _x hx => hH.1.2 (Or.inr hx))
  obtain ⟨t,c,ht⟩ := S.original_abelian_normal_specialLinearFour_graph
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn e
  let ts := (QuotientGroup.mk' (pCore 2 H)) (ι t)
  refine ⟨t,c,?_⟩
  intro g
  have hgraph : graphSL F₄ g = Matrix.SpecialLinearGroup.inverseTranspose g := by
    apply Subtype.ext
    exact (Matrix.adjugate_transpose g.val).symm
  have hh := DFunLike.congr_fun ht g
  change e (MulAut.conjNormal ts⁻¹ (e.symm g)) =
    linearConjSL F₄ c (graphSL F₄ g) at hh
  rw [hgraph] at hh
  have he := congrArg (fun x : SL(3,F₄) => (e.symm x).val) hh
  rw [e.symm_apply_apply,MulAut.conjNormal_apply,inv_inv] at he
  change (e.symm g).val * ts = ts * _
  calc
    _ = ts * (ts⁻¹ * (e.symm g).val * ts) := by group
    _ = _ := congrArg (ts * ·) he

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- Construct the model marking and graph actor from the original special-linear row. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_graph_model
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    let ι : T →* H := inclusion (fun _x hx => hH.1.2 (Or.inr hx))
    ∃ e : actorImage H K ≃* SL(3,F₄),
      ∃ t : T, ∃ c : Matrix.GeneralLinearGroup (Fin 3) F₄,
        ∀ g : SL(3,F₄),
          (e.symm g).val * (QuotientGroup.mk' (pCore 2 H)) (ι t) =
            (QuotientGroup.mk' (pCore 2 H)) (ι t) *
              (e.symm (linearConjSL F₄ c (Matrix.SpecialLinearGroup.inverseTranspose g))).val := by
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let eF : F ≃+* F₄ := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hcard,Representation.SL2FourNatural.card_field])
  let e : actorImage H K ≃* SL(3,F₄) :=
    ((componentStarEquiv H K hKH hK).symm.trans eK).trans (Atlas.fieldEquivSL 3 eF)
  exact ⟨e,S.original_abelian_normal_specialLinearFour_graph_relation
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn e⟩

end CFSG.Quasithin.Chapter12.Section06
