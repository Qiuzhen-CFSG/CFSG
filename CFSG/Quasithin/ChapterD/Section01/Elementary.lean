module

public import CFSG.Quasithin.ChapterD.Section01.Configuration
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.Representation.BinaryOffender.Ratio

/-!
# The elementary reductions in D.1.2

This file records the group-theoretic part of Aschbacher--Smith D.1.2.  The
conjugate span is kept as the literal span of the conjugates in the ambient
group.  The Thompson equalities use the rank-indexed family from B.2.2, whose
zero term is definitionally identified with the existing maximum-order
Thompson subgroup.

The two representation-theoretic facts used in the printed proof are exposed
as small contracts.  In particular, the pairwise quadratic rank comparison and
the universal B.6.8/B.6.9 inputs are not silently replaced by stronger local
certificates.  The source owner can discharge those contracts from the actual
module and quotient maps.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), D.1.2,
printed pp. 172--173 (PDF pp. 183--184).
-/

namespace CFSG.Quasithin.ChapterD

open Subgroup
open CFSG.Quasithin.ChapterB
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The two definitions of the conjugate span agree. -/
public theorem conjugateSpan_eq_conjugateSpanBy (H V : Subgroup G) :
    conjugateSpan H V = Subgroup.conjugateSpanBy V H := by
  symm
  exact Subgroup.conjugateSpanBy_eq_iSup_conj V H

/-- If the seed centralizes its actual conjugate span, the span is elementary.

The centralizer hypothesis is the literal conclusion of the two-conjugate
commutator calculation in the proof of D.1.2(1). -/
public theorem conjugateSpan_elementary_of_centralizer
    (H V : Subgroup G) [IsElementaryAbelian 2 V]
    (hcentral : V ≤ centralizer (conjugateSpan H V : Set G)) :
    IsElementaryAbelian 2 (conjugateSpan H V) := by
  rw [conjugateSpan_eq_conjugateSpanBy]
  have hcentral' : V ≤ centralizer (Subgroup.conjugateSpanBy V H : Set G) := by
    simpa only [conjugateSpan_eq_conjugateSpanBy] using hcentral
  let : IsMulCommutative ↥(Subgroup.conjugateSpanBy V H) :=
    (Subgroup.conjugateSpanBy_commutative_iff V H).mpr hcentral'
  exact Subgroup.conjugateSpanBy_elementary_of_commutative V H

/-- A pair of elementary abelian subgroups gives the ratio bound used in
D.1.2(1), once the printed rank comparison has been established. -/
public theorem quadratic_pair_actionRatio_le_one
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [Finite H] (ρ : Representation (ZMod 2) H X) (A : Subgroup H)
    (hA : Representation.BinaryOffender.IsElementaryTwo A)
    (_hquadratic : Representation.BinaryOffender.IsQuadratic ρ A)
    (hcodim : Representation.BinaryOffender.fixedCodim ρ A ≤
      Representation.BinaryOffender.rank A) :
    Representation.BinaryOffender.actionRatio ρ A ≤ 1 := by
  exact (Representation.BinaryOffender.actionRatio_le_one_iff ρ hA).mpr hcodim

/-- The global quadratic ratio is at most one when one actual pair actor has
quadratic action and satisfies the printed rank comparison. -/
public theorem quadraticRatio_le_one_of_quadratic_pair
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [Finite H] (ρ : Representation (ZMod 2) H X) (A : Subgroup H)
    (hA : Representation.BinaryOffender.IsElementaryTwo A)
    (_hquadratic : Representation.BinaryOffender.IsQuadratic ρ A)
    (hcodim : Representation.BinaryOffender.fixedCodim ρ A ≤
      Representation.BinaryOffender.rank A) :
    Representation.BinaryOffender.quadraticRatio ρ ≤ 1 := by
  exact (Representation.BinaryOffender.quadraticRatio_le_one_iff ρ).mpr
    ⟨A, ⟨hA, hcodim⟩, _hquadratic⟩

/-- The ratio form of the two-conjugate argument in D.1.2(1).  The
representation `ρ` must be the actual internal action image, and `hbad` is
the source rank calculation: a non-elementary span supplies one of the two
conjugate actors with quadratic action and the displayed rank comparison. -/
public theorem qrc_elementary_span_of_ratio_gt_one
    {G₁ G₂ T V : Subgroup G} [Finite G]
    (_h : QRCConfiguration G₁ G₂ T V)
    (_hVcore : V ≤ twoCoreIn G₂)
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [Finite H] (ρ : Representation (ZMod 2) H X)
    (hq : 1 < Representation.BinaryOffender.quadraticRatio ρ)
    (hbad : ¬ IsElementaryAbelian 2 (conjugateSpan G₂ V : Subgroup G) →
      ∃ A, Representation.BinaryOffender.IsElementaryTwo A ∧
        Representation.BinaryOffender.IsQuadratic ρ A ∧
        Representation.BinaryOffender.fixedCodim ρ A ≤
          Representation.BinaryOffender.rank A) :
    IsElementaryAbelian 2 (conjugateSpan G₂ V) := by
  by_contra hU
  obtain ⟨A, hA, hquad, hcodim⟩ := hbad hU
  have hle : Representation.BinaryOffender.quadraticRatio ρ ≤ 1 :=
    quadraticRatio_le_one_of_quadratic_pair ρ A hA hquad hcodim
  exact (not_le_of_gt hq) hle

/-- D.1.2(1), in the source form needed by the parent assembly.  The
hypothesis `hcentral` is the result of the two-conjugate commuting and rank
comparison argument; it is kept explicit so that the representation and the
actual quotient action cannot be confused with an unrelated classifier. -/
public theorem qrc_elementary_span
    {G₁ G₂ T V : Subgroup G} (h : QRCConfiguration G₁ G₂ T V)
    (_hVcore : V ≤ twoCoreIn G₂)
    (hcentral : V ≤ centralizer (conjugateSpan G₂ V : Set G)) :
    IsElementaryAbelian 2 (conjugateSpan G₂ V) := by
  let : IsElementaryAbelian 2 V := h.module_elementary
  exact conjugateSpan_elementary_of_centralizer G₂ V hcentral

/-- The two-core of a subgroup is below every ambient Sylow subgroup supplied
by the configuration. -/
public theorem twoCoreIn_le_sylow_right
    {G₁ G₂ T V : Subgroup G} (h : QRCConfiguration G₁ G₂ T V) :
    twoCoreIn G₂ ≤ T := by
  rcases h.sylow_right with ⟨S, hS⟩
  unfold twoCoreIn
  exact (Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal S)).trans_eq hS

/-- The corresponding inclusion for the first two-core. -/
public theorem twoCoreIn_le_sylow_left
    {G₁ G₂ T V : Subgroup G} (h : QRCConfiguration G₁ G₂ T V) :
    twoCoreIn G₁ ≤ T := by
  rcases h.sylow_left with ⟨S, hS⟩
  unfold twoCoreIn
  exact (Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal S)).trans_eq hS

/-- D.1.2(2): the Thompson equalities from the centralizer containment.  The
positive-rank premise records the source's nontrivial two-local situation; it
is not inferred from the degenerate literal D.1.1 record. -/
public theorem qrc_thompson_equalities
    {G₁ G₂ T V : Subgroup G} [Finite G]
    (h : QRCConfiguration G₁ G₂ T V)
    (hJcentral : thompsonJ T 0 ≤ centralizer (V : Set G))
    (hrank : 0 < twoRank T)
    (hR₂T : twoCoreIn G₂ ≤ T) :
    thompsonJ T 0 = thompsonJ (twoCoreIn G₁) 0 ∧
      thompsonJ T 0 = thompsonJ (twoCoreIn G₁ ⊔ twoCoreIn G₂) 0 := by
  have hRT : twoCoreIn G₁ ≤ T := twoCoreIn_le_sylow_left h
  have hJR : thompsonJ T 0 ≤ twoCoreIn G₁ := by
    have hJT : thompsonJ T 0 ≤ T ⊓ centralizer (V : Set G) :=
      le_inf (thompsonJ_le T 0) hJcentral
    rw [← h.core_eq_centralizer] at hJT
    exact hJT
  have h₁ := lemma_B_2_3_3 T (twoCoreIn G₁) hrank hJR hRT
  have hJjoin : thompsonJ T 0 ≤ twoCoreIn G₁ ⊔ twoCoreIn G₂ :=
    hJR.trans le_sup_left
  have hjoinT : twoCoreIn G₁ ⊔ twoCoreIn G₂ ≤ T := sup_le hRT hR₂T
  have h₂ := lemma_B_2_3_3 T (twoCoreIn G₁ ⊔ twoCoreIn G₂)
    hrank hJjoin hjoinT
  exact ⟨h₁, h₂⟩

/-- The source normality contradiction behind D.1.2(3).  The two normalizer
containments are relative to the original members `G₁` and `G₂`, exactly as in
D.1.1(3), rather than ambient normality in an unspecified larger group. -/
public theorem qrc_thompson_not_le_rightCore
    {G₁ G₂ T V : Subgroup G} [Finite G] (h : QRCConfiguration G₁ G₂ T V)
    (hEq : thompsonJ T 0 = thompsonJ (twoCoreIn G₁) 0 ∧
      thompsonJ T 0 = thompsonJ (twoCoreIn G₁ ⊔ twoCoreIn G₂) 0)
    (hJne : thompsonJ (twoCoreIn G₁) 0 ≠ ⊥)
    (hN₁ : G₁ ≤ normalizer (thompsonJ (twoCoreIn G₁) 0 : Set G))
    (hN₂ : G₂ ≤ normalizer (thompsonJ (twoCoreIn G₁) 0 : Set G)) :
    ¬ thompsonJ (twoCoreIn G₁) 0 ≤ twoCoreIn G₂ := by
  intro hJR₂
  have hJTR : thompsonJ T 0 ≤ twoCoreIn G₂ := by
    calc
      thompsonJ T 0 = thompsonJ (twoCoreIn G₁) 0 := hEq.1
      _ ≤ twoCoreIn G₂ := hJR₂
  have hbot := h.eq_bot_of_normalized
    (show thompsonJ (twoCoreIn G₁) 0 ≤ twoCoreIn G₁ from
      (thompsonJ_le (twoCoreIn G₁) 0)) hN₁ hN₂
  apply hJne
  exact hbot

/-- If the right Sylow subgroup is normal in `G₂`, its two-core image is the
same Sylow subgroup.  Normality is relative to the displayed subgroup `G₂`.
-/
public theorem twoCoreIn_eq_sylow_of_normal_right
    {G₂ T : Subgroup G}
    (S : Sylow 2 G₂)
    (hS : (S : Subgroup G₂).map G₂.subtype = T)
    (hSnormal : (S : Subgroup G₂).Normal) :
    twoCoreIn G₂ = T := by
  have hle : twoCoreIn G₂ ≤ T := by
    unfold twoCoreIn
    exact (Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal S)).trans_eq hS
  let : (S : Subgroup G₂).Normal := hSnormal
  have hSp : (S : Subgroup G₂) ≤ pCore 2 G₂ := by
    apply le_sSup
    exact ⟨inferInstance, S.isPGroup'⟩
  have hge : T ≤ twoCoreIn G₂ := by
    rw [← hS]
    exact Subgroup.map_mono hSp
  exact le_antisymm hle hge

/-- D.1.2(3), the nonnormality deduction after the Thompson comparison. -/
public theorem qrc_right_sylow_not_normal
    {G₁ G₂ T : Subgroup G} [Finite G]
    (hJnot : ¬ thompsonJ (twoCoreIn G₁) 0 ≤ twoCoreIn G₂)
    (hJleT : thompsonJ (twoCoreIn G₁) 0 ≤ T)
    (S : Sylow 2 G₂)
    (hS : (S : Subgroup G₂).map G₂.subtype = T) :
    ¬ (S : Subgroup G₂).Normal := by
  intro hSn
  apply hJnot
  rw [twoCoreIn_eq_sylow_of_normal_right S hS hSn]
  exact hJleT

/-- D.1.2(4): convert the unique maximal-overgroup field of the configuration
into the literal B.6.1 minimal-parabolic predicate. -/
public theorem qrc_minimal_parabolic_of_unique_maximal
    {G₁ G₂ T V : Subgroup G} (h : QRCConfiguration G₁ G₂ T V)
    (S : Sylow 2 G₂) (hS : (S : Subgroup G₂).map G₂.subtype = T)
    (hSnotnormal : ¬ (S : Subgroup G₂).Normal) :
    ChapterB.IsMinimalParabolicOver S (⊤ : Subgroup G₂) := by
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  refine ⟨?_, hSnotnormal⟩
  rcases h.unique_maximal with ⟨M, hM, huniq⟩
  refine ⟨M, ⟨hM.1, ?_⟩, ?_⟩
  · exact (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective G₂)).mp
      (hS ▸ hM.2)
  · intro N hN
    apply huniq N
    refine ⟨hN.1, ?_⟩
    exact (hS ▸ (Subgroup.map_le_map_iff_of_injective
      (Subgroup.subtype_injective G₂)).mpr hN.2)

/-- D.1.2(5), conditional form.  `hB68` and `hB69` are the exact universal
inputs supplied by B.6.8(6c) and B.6.9(1), respectively.  They are kept as a
separate theorem so a later source assembly can discharge them under its SQTK
hypotheses without weakening the generic D.1.2 statement. -/
public theorem qrc_reduced_module_ratio_ge_one_of_B6
    {G₂ X : Type*} [Group G₂] [Group X] [AddCommGroup X]
    [Module (ZMod 2) X] [Finite G₂]
    (_Wsub : Subgroup G₂)
    (hB68 : Chapter6.Source.reducedFamily (⊤ : Subgroup G₂) _Wsub)
    (ρ : Representation (ZMod 2) G₂ X)
    (hB69 : 1 ≤ Representation.BinaryOffender.quadraticRatio ρ) :
    Chapter6.Source.reducedFamily (⊤ : Subgroup G₂) _Wsub ∧
      1 ≤ Representation.BinaryOffender.quadraticRatio ρ := by
  exact ⟨hB68, hB69⟩

end CFSG.Quasithin.ChapterD
