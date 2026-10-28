module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SeedSource
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NaturalOrbitSpan
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleFiveMarker
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.RankOne
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Saturation

/-!
# Noncentral Thompson-fixed witnesses before block reconstruction

The normal rank-one action is sufficient to find a noncentral fixed vector
in the original moved subgroup. In the natural SL₂ branch, the proved alpha
decomposition and its orbit span force the witness. In the distinct S₅/A₅
permutation branch, the Thompson and residual fixed codimensions are two
and four. Both arguments retain the actual central kernel and require no
block hypothesis. B.5.1 and the minimal-parabolic recognition supply the
full disjunction, so no natural-coordinate premise remains in the final
export.

Source: Aschbacher--Smith C.1.16(3), pp.125--126, and its application in
15.1.20(2), pp.1094--1095; B.5.1, B.6.9--10 and C.1.24.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

omit [Finite G] in
private theorem fixed_noncentral_of_alpha_span (R W K : Subgroup G)
    (ha : thompsonAlpha R = (W ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ⊔
      (thompsonAlpha R ⊓ centralizer (K : Set G)))
    (hs : conjugateSpanBy (thompsonAlpha R) K =
      W ⊔ (thompsonAlpha R ⊓ centralizer (K : Set G)))
    (hw : ¬ W ≤ centralizer (K : Set G)) :
    ¬ W ⊓ centralizer (elementaryAbelianMaxJ R : Set G) ≤ centralizer (K : Set G) := by
  intro hc
  have hac : thompsonAlpha R ≤ centralizer (K : Set G) :=
    ha.le.trans (sup_le hc inf_le_right)
  have hn : K ≤ normalizer (centralizer (K : Set G) : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_centralizer K)
  exact hw (le_sup_left.trans (hs.symm.le.trans (conjugateSpanBy_le hac hn)))

private theorem normal_layer_moved_fixed_noncentral
    {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hF : 2 < Nat.card F)
    (f : Additive (⁅U,pResidual 2 G⁆ : Subgroup G) →ₗ[ZMod 2] (Fin 2 → F))
    (hf : Function.Surjective f)
    (he : ∀ (g : G) (hg : q g ∈ L) (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        SL2NaturalOffenders.NoStrong.natural (e ⟨q g,hg⟩) (f v))
    (hk : ∀ (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G)) :
    ¬ (⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
        centralizer (pResidual 2 G : Set G) := by
  apply fixed_noncentral_of_alpha_span (T : Subgroup G) _ (pResidual 2 G)
    (RankOneBaumann.normal_layer_moved_baumann_sylow_and_alpha
      T hP U hU hJ q hq hker L e hF f hf he hk).2
    (RankOneBaumann.normal_layer_moved_thompsonAlpha_orbit_span
      T hP U hU hJ q hq hker L e hF f hf he hk)
  intro hc
  obtain ⟨v,hv⟩ := exists_ne (0 : Fin 2 → F)
  obtain ⟨w,rfl⟩ := hf v
  exact hv ((hk w).mpr (hc w.toMul.property))

/-- The natural B.5.1 moved section has a noncentral Thompson-fixed vector. -/
theorem quasisimple_linear_fixed_noncentral
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
 :
    ¬ (⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
        centralizer (pResidual 2 G : Set G) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  let := hqs
  let : IsSimpleGroup (A ⧸ center A) := hqs.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  obtain ⟨e⟩ := hnatural
  have hF := perfect_linear_two_field_large F e.groupEquiv
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  have hX : A.map Y.subtype = (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hL
  let L := A.map Y.subtype
  let : L.Normal := by change (A.map Y.subtype).Normal; infer_instance
  let eg := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e.groupEquiv
  apply normal_layer_moved_fixed_noncentral T hP U hU hJ q hq hker
    L eg hF (sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ e)
    (sourceMovedQuotientMap_surjective U q hq hker Y A s (pResidual 2 G) hX _ e) ?_
    (sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ e)
  intro g hg v
  let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm ⟨q g,hg⟩
  have ha : q g = (a:Y) := (congrArg Subtype.val
    ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply ⟨q g,hg⟩)).symm
  exact sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ e g a ha v

private theorem five_fixed_noncentral
    (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (f : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (f v))
    (hk : f.ker = fixedSpace (NormalElementaryQuotient.representation U q hq hker)
      ((pResidual 2 G).map q)) :
    ¬ U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
        centralizer (pResidual 2 G : Set G) := by
  have hres := SymmetricFive.source_residual_image q hq
  have hfix : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hker g v = v := by
    intro v hv g hg
    have hv' : v ∈ fixedSpace (NormalElementaryQuotient.representation U q hq hker)
        ((pResidual 2 G).map q) := hk ▸ hv
    exact hv' ⟨g,hres.symm ▸ hg⟩
  have hc := SymmetricFive.source_fixedCodim U T hUT q hq hker f hf he hfix hJ
  obtain ⟨a,ha⟩ := SymmetricFive.source_thompson_conjugate U T hUT q hq hker f hf he hfix hJ
  have hsmall : BaumannArgument.fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) = 2 := by
    rw [BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,hc,ha,
      fixedCodim_map_conj,
      ChapterB.Offenders.Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl]
  have hlarge : BaumannArgument.fixedCodim U (pResidual 2 G) = 4 := by
    rw [BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,hc,hres,
      SymmetricFive.fixedCodim_alternating]
  intro hle
  have hbound : U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      U ⊓ centralizer (pResidual 2 G : Set G) := le_inf inf_le_left hle
  have hcard := Nat.card_le_card_of_injective _ (inclusion_injective hbound)
  have hlog := Nat.log_mono_right (b := 2) hcard
  have hdim : BaumannArgument.fixedCodim U (pResidual 2 G) ≤
      BaumannArgument.fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) :=
    Nat.sub_le_sub_left hlog _
  rw [hsmall,hlarge] at hdim
  omega

/-- The actual B.5.1 rank-one alternatives supply a noncentral Thompson-fixed
vector in the original moved subgroup. The central kernel is retained. -/
theorem quasisimple_rankOne_fixed_noncentral
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      ((NormalElementaryQuotient.representation U q hq hker).comp
        (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))) :
    ¬ (⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
        centralizer (pResidual 2 G : Set G) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule ρ := by
    obtain hc | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hc.1)).elim
    · exact hff
  rcases source_offender_quasisimple_rank_one ρ (T.mapSurjective hq) hp hff hcore hqs c
    with ⟨F,hnat⟩ | ⟨e⟩
  · exact quasisimple_linear_fixed_noncentral T hP U hU hJ q hq hker hqs c.sectionData F hnat
  · obtain ⟨e⟩ := e
    let W := ⁅U,pResidual 2 G⁆
    have hW := hU.moved U
    let := hW.elementary
    have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
      rwa [hU.centralizer_moved_eq U]
    obtain ⟨q5,hq5,hk5,f,hf,he,hk⟩ := quasisimple_five_source_marker
      T hP U hU hJ q hq hker hqs c.sectionData e
    exact five_fixed_noncentral T W (hW.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T))
      hJW q5 hq5 hk5 f hf he hk

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
