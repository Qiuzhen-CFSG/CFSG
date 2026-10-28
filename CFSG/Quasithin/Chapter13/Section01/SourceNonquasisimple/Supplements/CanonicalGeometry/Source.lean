module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Frattini
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Source

/-!
# Original 13.1.9 applications of the canonical Frattini geometry

The proved radical action kernel removes all kernel assumptions from
supplement invariance. The original Sylow assertion then supplies local
membership and O₂(L_R T)=R, and every supplement has its residual Frattini
product. Quasisimplicity of the canonical two-core quotient identifies
all residual normalizers and gives the literal setwise radical products.
The same source PSL₂(p) model is retained on the canonical radical quotient.

The source Sylow/inversion analysis, canonical faithfulness and qrc
intersection argument still require proof. These conditional applications
do not establish all of 13.1.9 or its Thompson-movement conclusion.
Source: Aschbacher--Smith 13.1.8--9, printed pp.868--869.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

omit [Finite G] in
private theorem core_le_of_join_core_eq (Y S R : Subgroup G)
    (hSY : S ≤ normalizer (Y : Set G)) (hc : (Y ⊔ S).pCoreIn 2 = R) :
    Y.pCoreIn 2 ≤ R := by
  have hm : Y.pCoreIn 2 ≤ (Y ⊔ S).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le Y.le_normalizer hSY)
  exact hm.trans_eq hc

/-- Every actual radical supplement is T-invariant and has exactly the
same section centralizer, without an extra invariance premise. -/
theorem supplements_invariant_source (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    {B : Subgroup G} (hB : B ∈ radicalSupplements T L) :
    (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      radicalSylowCentralizer T B = radicalSylowCentralizer T L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hTB := supplement_invariant hTL hB
  have hk := (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1
  exact ⟨hTB,supplement_radicalSylowCentralizer hTL hTB hk hB.2⟩

/-- The literal source Frattini geometry, conditional only on the original
Sylow assertion. This establishes local membership, the radical product,
and O₂(L_R T)=R; it does not identify the canonical quotient. -/
theorem canonical_frattini_geometry_source (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hs : IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype)) :
    canonicalSupplement T L ∈ radicalSupplements T L ∧
      (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L ∧
      ∀ B ∈ radicalSupplements T L,
        (solvableRadical B).map B.subtype ⊔
          normalizerResidual B (radicalSylowCentralizer T L) = B := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hk := (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1
  have hfr := canonical_frattini_of_radical_sylow hL.1.1 hTL hk hs
  exact ⟨⟨canonical_mem_local_of_radical_sylow T hL.1.1 hTL hs,hfr⟩,
    canonical_join_core_of_frattini T hTL hk hfr,
    fun _ hB => supplements_frattini_of_radical_sylow hTL hk hs hB⟩

/-- The source comparison for all actual supplements. Only the original
radical Sylow assertion and quasisimplicity of the canonical quotient
remain; neither supplement uniqueness nor Thompson movement is assumed. -/
theorem canonical_supplement_comparison_source (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hs : IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype))
    (hq : IsQuasisimple (XiQuotient (canonicalSupplement T L))) :
    canonicalSupplement T L ∈ radicalSupplements T L ∧
      (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L ∧
      ∀ B ∈ radicalSupplements T L,
        normalizerResidual B (radicalSylowCentralizer T L) = canonicalSupplement T L ∧
        (solvableRadical B).map B.subtype ⊔ canonicalSupplement T L = B ∧
        canonicalSupplement T L ≤ B ∧
        (((solvableRadical B).map B.subtype : Subgroup G) : Set G) *
          (canonicalSupplement T L : Set G) = (B : Set G) := by
  obtain ⟨hY,hcore,hfr⟩ := canonical_frattini_geometry_source h hmany hL hn hs
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hk := (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1
  let Y : Subgroup G := canonicalSupplement (T : Subgroup G) L
  let R : Subgroup G := radicalSylowCentralizer (T : Subgroup G) L
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    sylow_normalizes_canonicalSupplement (T := (T : Subgroup G)) (L := L) hTL
  have hcoreY : Y.pCoreIn 2 ≤ R :=
    core_le_of_join_core_eq (G := G) Y (T : Subgroup G) R hTY hcore
  refine ⟨hY,hcore,?_⟩
  intro B hB
  have he := supplement_residual_eq_canonical (T := (T : Subgroup G)) (L := L) (B := B)
    hTL hk hB (hfr B hB) hcoreY hq
  have hg := hfr B hB
  rw [he] at hg
  have hYB : canonicalSupplement T L ≤ B := le_sup_right.trans hg.le
  refine ⟨he,hg,hYB,?_⟩
  rw [← coe_mul_of_right_le_normalizer_left _ _
    (hYB.trans (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (solvableRadical B)))),hg]

/-- The same original PSL₂(p) acts on the canonical radical quotient.
The inversion branch must still identify its radical with its two-core. -/
theorem canonical_radical_quotient_source (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hs : IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL
      (canonicalSupplement T L ⧸ solvableRadical (canonicalSupplement T L)) 2 p := by
  have hY := (canonical_frattini_geometry_source h hmany hL hn hs).1
  obtain ⟨p,hp,hp3,ha⟩ := radical_supplements_action_source h hmany hL hn
  exact ⟨p,hp,hp3,(ha _ hY).1⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
