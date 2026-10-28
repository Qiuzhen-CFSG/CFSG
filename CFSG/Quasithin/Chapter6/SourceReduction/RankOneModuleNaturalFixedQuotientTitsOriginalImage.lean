module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsOriginalOmega

/-!
# The image of the original Hermitian module in the Tits quotient

Every elementary subgroup in the actual normal Tits extension belongs to
its same normal component. The certified rank-five bound therefore limits
the image of the full original Hermitian module modulo O₂(KT) to order 32.
The quotient map and its entire kernel remain literal.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666; GM04 Table13.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
open ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The full original Hermitian module has image of order at most 32 in
the literal quotient by the entire two-core of KT. -/
theorem original_hermitian_tits_module_image_card_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    let J := K ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 J)
    Nat.card (((reducedSubgroup (L ⊔ (T : Subgroup G))).subgroupOf J).map q) ≤ 32 := by
  let J := K ⊔ (T : Subgroup G)
  let C := K.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let q := QuotientGroup.mk' (pCore 2 J)
  let N := C.map q
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let U := (B.subgroupOf J).map q
  have hTK := original_hermitian_sylow_normalizes_tits_component
    h hout hm hM₁ hCM₁ hK hnot hq e
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let ec : C ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eqc := QuotientGroup.congr (pCore 2 C) (pCore 2 K) ec (pCore_map_iso 2 ec)
  let := hq
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv eqc.symm
  have hgen : C ⊔ (P : Subgroup J) = ⊤ := by
    change K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  obtain ⟨f,_,hcN⟩ := Tits.marked_core_quotient C
    (isPGroup_quotient_of_sup_eq_top C (P : Subgroup J) P.isPGroup' hgen)
    ((coreCentralQuotientCongr ec).trans e)
  let : N.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 B := (h.reduced_enlargement.rankOneInput hout).reduced.2.1
  let : IsElementaryAbelian 2 (B.subgroupOf J) := IsElementaryAbelian.comap_of_injective
    J.subtype J.subtype_injective B
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map q
  have hUN : U ≤ N := elementary_le_normal_tits N U f hcN inferInstance
  let E := (U.subgroupOf N).map f.toMonoidHom
  have he : IsElementaryAbelian 2 E := by
    let : IsElementaryAbelian 2 (U.subgroupOf N) :=
      IsElementaryAbelian.comap_of_injective N.subtype N.subtype_injective U
    exact IsElementaryAbelian.map f.toMonoidHom
  have hb := (primeRank_le_iff_elementary_card_le Tits.ParrottGroup).mp
    parrott_two_rank_le_five E he
  rw [card_map_of_injective f.injective,
    Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv] at hb
  exact hb

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
