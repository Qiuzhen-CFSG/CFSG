module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.QuotientSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.ShortImage

/-!
# C.1.27 with the B.1.13 selection discharged

The internal module is the literal full orbit of the original Sylow omega-center.
Its faithful centralizer-quotient action has the original group as an SQTK cover.
The short-image lemma supplies quasisimplicity or order three; subnormality maps
from the original local overgroup. B.1.13 now selects the actual quotient block,
and the proved kernel/module lift constructs the ambient block.

The remaining B.6.9 inputs are exactly U(K) support and the source local
best-offender commutator identity. No quotient selection or recognition is assumed.
Source: Aschbacher--Smith C.1.27, pp.132--133.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
open ChapterB SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem map_local_subnormal {Q : Type*} [Group Q] (q : G →* Q)
    (K T : Subgroup G) (hs : (K.subgroupOf (K ⊔ T)).IsSubnormal) :
    ((K.map q).subgroupOf (K.map q ⊔ T.map q)).IsSubnormal := by
  let H := K ⊔ T
  have hm : ((K.subgroupOf H).map (q.subgroupMap H)) =
      (K.map q).subgroupOf (H.map q) := by
    apply map_injective (f := (H.map q).subtype) (H.map q).subtype_injective
    have he : (H.map q).subtype.comp (q.subgroupMap H) = q.comp H.subtype := rfl
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (map_mono (show K ≤ H from le_sup_left))]
  have hh := hs.map (q.subgroupMap_surjective H)
  rw [hm] at hh
  change ((K.map q).subgroupOf ((K ⊔ T).map q)).IsSubnormal at hh
  rw [Subgroup.map_sup] at hh
  exact hh

/-- Original C.1.27 block lifting with B.1.13 discharged on the literal
centralizer quotient. The two retained hypotheses are the earlier B.6.9
support and local-offender movement on that same action. -/
theorem source_block_of_local_offender_movement
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (K V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hV : V = normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hK : IsShort K) (hs : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hU : (blockU K).map K.subtype ≤ V)
    (hmove : let q := QuotientGroup.mk' (centralizer (V : Set G));
      let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _);
      K.map q = ⁅K.map q, generatedBy {A | IsBestOffender ρ A}
        ((T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V : Set G)))) :
          Subgroup (G ⧸ centralizer (V : Set G)))⁆) :
    ∃ L : Subgroup G, K ≤ L ∧ IsBlock L ∧ (blockU L).map L.subtype ≤ V ∧
      let q := QuotientGroup.mk' (centralizer (V : Set G));
      L.map q = K.map q ∨ Nonempty (L.map q ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (L.map q ≃* alternatingGroup (Fin 7)) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V : Set G)))
  have hv : IsPReduced 2 V := hV ▸ omegaCenter_normalClosure_reduced T hchar
  have hq : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple (G ⧸ centralizer (V : Set G))) :=
    ⟨{ Cover := G, kernel := centralizer (V : Set G), sqtk := hG, equiv := MulEquiv.refl _ }⟩
  obtain ⟨B,hB,hKB,hkind,hsel,hm⟩ := exists_subnormal_container_of_sqtk_quotient ρ
    hA hC h4 hq (NormalElementaryQuotient.representation_injective V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) hv.quotient_pCore_eq_bot
      (K.map q) S (short_image_kind V K hK hU)
      (map_local_subnormal q K (T : Subgroup G) hs) hmove
  subst V
  obtain ⟨L,hKL,hL,hUL,hLB⟩ := source_block_of_quotient_selection T hchar
    (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)
    (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left) hs hK hU B hB hKB hkind hsel
  refine ⟨L,hKL,hL,hUL,?_⟩
  change L.map q = K.map q ∨ _
  rw [hLB]
  exact hm.imp Eq.symm id

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
