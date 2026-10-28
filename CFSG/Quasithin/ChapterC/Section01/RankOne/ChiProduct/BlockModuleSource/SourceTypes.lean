module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.ProperSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SameImage

/-!
# Original local seeds give actual ambient χ or exceptional blocks

B.1.13 selects the literal component image, C.1.27 lifts it to an ambient
block, and the module-source dispatcher determines its type. Equal quotient
images give equality of the original groups, so the seed's existing χ-type
applies directly. The only unproved local inputs retained here are the
earlier B.6.9 support and full best-offender movement on the same action.

Source: Aschbacher--Smith C.1.27--28, printed pp.132--134.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
open ChapterB SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem image_local_subnormal {Q : Type*} [Group Q] (q : G →* Q)
    (K T : Subgroup G) (hs : (K.subgroupOf (K ⊔ T)).IsSubnormal) :
    ((K.map q).subgroupOf (K.map q ⊔ T.map q)).IsSubnormal := by
  let H := K ⊔ T
  have he : (K.subgroupOf H).map (q.subgroupMap H) = (K.map q).subgroupOf (H.map q) := by
    apply map_injective (H.map q).subtype_injective
    have hh : (H.map q).subtype.comp (q.subgroupMap H) = q.comp H.subtype := rfl
    rw [map_map,hh,← map_map,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (map_mono (show K ≤ H from le_sup_left))]
  have hh := hs.map (q.subgroupMap_surjective H)
  rw [he] at hh
  change ((K.map q).subgroupOf ((K ⊔ T).map q)).IsSubnormal at hh
  rw [Subgroup.map_sup] at hh
  exact hh

/-- The original local χ seed produces an ambient χ or exceptional A₇ block.
The quotient selection, module identification and all B.4 rows are discharged. -/
theorem source_chi_or_exceptional_block
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (K V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hV : V = normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hK : IsChiBlock K) (hs : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hU : (blockU K).map K.subtype ≤ V)
    (hmove : let q := QuotientGroup.mk' (centralizer (V : Set G));
      let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _);
      K.map q = ⁅K.map q, generatedBy {A | IsBestOffender ρ A}
        ((T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V : Set G)))) :
          Subgroup (G ⧸ centralizer (V : Set G)))⁆) :
    ∃ L : Subgroup G, K ≤ L ∧ IsBlock L ∧ (blockU L).map L.subtype ≤ V ∧
      (IsChiBlock L ∨ IsExceptionalA7Block L) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V : Set G)))
  have hv : IsPReduced 2 V := hV ▸ omegaCenter_normalClosure_reduced T hchar
  have hQC := le_centralizer_iff.mp hv.le_centralizer_pCore
  have hQH : pCore 2 G ≤ K ⊔ (T : Subgroup G) :=
    pCore_isPGroup.le_sylow_of_normal T |>.trans le_sup_right
  have hcov : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple (G ⧸ centralizer (V : Set G))) :=
    ⟨{ Cover := G, kernel := centralizer (V : Set G), sqtk := hG, equiv := MulEquiv.refl _ }⟩
  have hf := NormalElementaryQuotient.representation_injective V q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hkind := ComponentSource.short_image_kind V K hK.short hU
  have hsub := image_local_subnormal q K (T : Subgroup G) hs
  have lift (B : Subgroup (G ⧸ centralizer (V : Set G)))
      (hb : B.IsSubnormal) (hKB : K.map q ≤ B)
      (hkindB : IsQuasisimple B ∨ Nat.card B = 3)
      (hsel : K.map q = B ∨ ⁅K.map q,B⁆ = B) :
      ∃ L : Subgroup G, K ≤ L ∧ IsBlock L ∧ (blockU L).map L.subtype ≤ V ∧ L.map q = B := by
    subst V
    exact source_block_of_quotient_selection T hchar le_sup_right le_sup_left hs hK.short hU
      B hb hKB hkindB hsel
  rcases ComponentSource.source_selection_of_sqtk_quotient ρ hA
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC) h4 hcov hf
      hv.quotient_pCore_eq_bot (K.map q) S hkind hsub hmove with hz | hc
  · obtain ⟨L,hKL,hL,hUL,hLK⟩ := lift (K.map q)
      (ComponentSource.subnormal_of_le_fitting_center _ hz.2) le_rfl (Or.inr hz.1) (Or.inl rfl)
    have he := eq_of_same_centralizer_image V (K ⊔ (T : Subgroup G)) K L
      le_sup_left hQH hs hK.short.twoPerfect hKL hL hUL hQC hLK.symm
    exact ⟨L,hKL,hL,hUL,Or.inl (he ▸ hK)⟩
  · obtain ⟨B,hB,hKB,hBK,_⟩ := hc
    obtain ⟨L,hKL,hL,hUL,hLB⟩ := lift B hB.1 hKB (Or.inl hB.2)
      (Or.inr ((commutator_comm _ _).trans hBK))
    by_cases he : K.map q = L.map q
    · have hEq := eq_of_same_centralizer_image V (K ⊔ (T : Subgroup G)) K L
        le_sup_left hQH hs hK.short.twoPerfect hKL hL hUL hQC he
      exact ⟨L,hKL,hL,hUL,Or.inl (hEq ▸ hK)⟩
    · refine ⟨L,hKL,hL,hUL,?_⟩
      apply block_type_of_proper_seed V hA hC h4 hG hv L hL hUL (K.map q) S
        (hLB.symm ▸ hB) (hLB.symm ▸ hBK) hkind hsub hmove (hLB.symm ▸ hKB) he

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
