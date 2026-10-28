module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Radical.Source
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.OddRadical
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension
public import Theory.GroupTheory.SolvableRadical.TwoCoreOddQuotient
public import GorensteinWalter.SL2UniversalCover

/-!
# The canonical radical intersection in 13.1.9

Write R=C_T(L/O∞(L)) and Y=N_L(R)^∞. The recovered Sylow and
Frattini geometry places a full Sylow two-subgroup of O∞(Y) in the
normal two-subgroup R∩Y. Thus Y/O₂(Y) has odd solvable radical.
The genuine A.3.6 common clauses make this quotient quasisimple.
Its radical quotient is the already constructed PSL₂(p), for p prime
and p>3; the prime-field central-cover theorem makes the radical kernel
a two-group, hence trivial. Consequently O∞(Y)=O₂(Y).

The normal two-extension YT then has O∞(YT)=O₂(YT)=R. Restricting
the solvable normal subgroup O∞(LT) to YT gives the literal intersection.
The actual two-core model and all canonical supplement comparisons follow.
This route does not need the separate original full-Fitting inverter,
supplement uniqueness, or Thompson movement.

Source: Aschbacher--Smith, 13.1.9, first proof paragraph, printed p.869;
A.3.6, pp.43--45; the prime-field covering result in I.1.3, pp.407--408.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The canonical quotient has odd radical because Y normalizes the full radical Sylow R. -/
theorem canonical_odd_radical_quotient (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    Odd (Nat.card (solvableRadical (XiQuotient (canonicalSupplement T L)))) := by
  let Y := canonicalSupplement (T : Subgroup G) L
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let W := Y ⊔ (T : Subgroup G)
  let A := (solvableRadical Y).map Y.subtype
  let D := (solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
    (L ⊔ (T : Subgroup G)).subtype
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hY := (canonical_frattini_geometry h hmany hL hn).1
  have hk := (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1
  have hAD : A ≤ D := ((supplement_radical hk hY.2).le.trans inf_le_right).trans
    (radical_le_join_radical hTL)
  have hAY : A ≤ Y := map_subtype_le _
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    sylow_normalizes_canonicalSupplement hTL
  have hWA : W ≤ normalizer (A : Set G) :=
    (sup_le Y.le_normalizer hTY).trans
      (normalizer_le_normalizer_characteristic_image Y (solvableRadical Y))
  let : (A.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hWA
  have hsA : IsSylowIn 2 ((T : Subgroup G) ⊓ A) A :=
    IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
      (hAY.trans le_sup_left) (inferInstance : (A.subgroupOf W).Normal).isSubnormal
  have hsY : IsSylowIn 2 (((T : Subgroup G) ⊓ A).subgroupOf Y) (solvableRadical Y) := by
    apply (IsSylowIn.map_iff Y.subtype Y.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (inf_le_right.trans hAY)]
    exact hsA
  have hSR : (T : Subgroup G) ⊓ A ≤ R := by
    dsimp only [R]
    rw [radicalSylowCentralizer_eq_inf_radical T hTL]
    exact inf_le_inf_left _ hAD
  have hYR : Y ≤ normalizer (R : Set G) := normalizerResidual_le_normalizer _ _
  have hcore : (T : Subgroup G) ⊓ A ≤ Y.pCoreIn 2 := by
    apply (le_inf hSR (inf_le_right.trans hAY)).trans
    exact le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (inf_le_left.trans (radicalSylowCentralizer_le _ _)))
      inf_le_right ((le_inf hYR Y.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  obtain ⟨S,hS⟩ := hsY
  have hSP : (S : Subgroup (solvableRadical Y)) ≤
      (pCore 2 Y).subgroupOf (solvableRadical Y) := by
    apply map_le_iff_le_comap.mp
    rw [hS]
    apply (map_le_map_iff_of_injective Y.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (inf_le_right.trans hAY)]
    exact hcore
  apply odd_radical_twoCore_quotient_iff.mpr
  exact Nat.not_even_iff_odd.mp (fun he => S.not_dvd_index
    ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hSP)))

/-- A.3.6 excludes the noncentral radical alternative in the literal canonical quotient. -/
theorem canonical_quasisimple (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsQuasisimple (XiQuotient (canonicalSupplement T L)) := by
  let Y := canonicalSupplement (T : Subgroup G) L
  have hY := (canonical_frattini_geometry h hmany hL hn).1.1
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hQ := uniqueness_local_quotient_sqtk h.simpleQTKE hY.2.2
  have hc := proposition_1_2_1_four_earlier_conclusion h36 hQ hY.1
  let C := radicalLocalImage T Y
  let e : XiQuotient Y ≃* C := radicalLocalQuotientEquiv hY
  let : Group.IsPerfect (Y.subgroupOf (Y ⊔ (T : Subgroup G))) := hY.1.perfect
  let : Group.IsPerfect C := Group.IsPerfect.map _
  have ho : Odd (Nat.card (solvableRadical C)) := by
    rw [← map_solvableRadical_equiv e]
    exact (Nat.card_congr (e.subgroupMap (solvableRadical (XiQuotient Y))).toEquiv) ▸
      canonical_odd_radical_quotient h hmany hL hn
  let : IsQuasisimple C := hc.2.isQuasisimple_of_odd_radical ho
  exact IsQuasisimple.of_mulEquiv e.symm

/-- The prime-field PSL₂ covering has a two-group kernel, killing the remaining radical. -/
theorem canonical_radical_eq_twoCore (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    solvableRadical (canonicalSupplement T L) = pCore 2 (canonicalSupplement T L) := by
  let Y := canonicalSupplement (T : Subgroup G) L
  let Q := XiQuotient Y
  let q := QuotientGroup.mk' (pCore 2 Y)
  let : IsQuasisimple Q := canonical_quasisimple h hmany hL hn
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
    infer_instance
  obtain ⟨p,hp,hp3,F,hF,hfin,hcard,⟨e⟩⟩ := canonical_radical_quotient h hmany hL hn
  let : Fact (3 < Nat.card F) := ⟨by simpa only [hcard] using hp3⟩
  let eQ : (Q ⧸ solvableRadical Q) ≃* PSL(2,F) :=
    (solvableRadicalQuotientEquiv q (QuotientGroup.mk'_surjective _)).symm.trans e
  let g : Covering Q PSL(2,F) :=
    { toMonoidHom := eQ.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical Q))
      surjective := eQ.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hg : g.toMonoidHom.ker = solvableRadical Q := by
    change (eQ.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical Q))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ eQ.injective,QuotientGroup.ker_mk']
  have hrp : IsPGroup 2 (solvableRadical Q) := hg ▸
    GorensteinWalter.PSL2Cover.kernel_isPGroup_of_card_prime F g (by simpa only [hcard] using hp)
  have hz : solvableRadical Q = ⊥ := by
    apply le_bot_iff.mp
    exact (le_sSup ⟨inferInstance,hrp⟩ : solvableRadical Q ≤ pCore 2 Q).trans_eq
      (pCore_quotient_pCore_eq_bot 2)
  rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _),hz]
  exact QuotientGroup.ker_mk' _

/-- The original intersection O∞(LT)∩YT is exactly R, with relative normality retained. -/
theorem canonical_radical_intersection (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype ⊓
        (canonicalSupplement T L ⊔ (T : Subgroup G)) = radicalSylowCentralizer T L := by
  let Y := canonicalSupplement (T : Subgroup G) L
  let W := Y ⊔ (T : Subgroup G)
  let C := Y.subgroupOf W
  let V := L ⊔ (T : Subgroup G)
  let D := (solvableRadical V).map V.subtype
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hTY := sylow_normalizes_canonicalSupplement hTL
  have hr := canonical_radical_eq_twoCore h hmany hL hn
  have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hTY)
  let e : C ≃* Y := subgroupOfEquivOfLe le_sup_left
  have hradC : IsPGroup 2 (solvableRadical C) := by
    have hm : (solvableRadical C).map e.toMonoidHom = pCore 2 Y := by
      rw [map_solvableRadical_equiv e,hr]
    exact (pCore_isPGroup.of_equiv (MulEquiv.subgroupCongr hm).symm).of_equiv
      (e.subgroupMap (solvableRadical C)).symm
  have hgen : C ⊔ (T : Subgroup G).subgroupOf W = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ W from le_sup_left)
      (show (T : Subgroup G) ≤ W from le_sup_right)]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (W ⧸ C) :=
    isPGroup_quotient_of_sup_eq_top C _ T.isPGroup'.comap_subtype hgen
  have hradW : solvableRadical W = pCore 2 W :=
    radical_eq_core_of_normal_two_quotient C hradC hquot
  have hWD : W ≤ normalizer (D : Set G) :=
    (sup_le_sup_right (canonicalSupplement_le _ _) _).trans
      (V.le_normalizer.trans (normalizer_le_normalizer_characteristic_image V (solvableRadical V)))
  let : (D.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hWD
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (V.subtype.subgroupMap_surjective (solvableRadical V))
  let : Group.IsSolvable (D.subgroupOf W) := Group.isSolvable_of_isSolvable_injective
    (f := W.subtype.subgroupComap D)
    (fun a b he => Subtype.ext (Subtype.ext (congrArg (fun x : D => (x : G)) he)))
  apply le_antisymm
  · have hm := map_mono (f := W.subtype)
      (le_solvableRadical (D.subgroupOf W) inferInstance inferInstance)
    rw [subgroupOf_map_subtype,hradW] at hm
    exact hm.trans_eq hcore
  · rw [radicalSylowCentralizer_eq_inf_radical T hTL]
    exact le_inf inf_le_right (inf_le_left.trans le_sup_right)

/-- The actual source PSL₂(p) model, now on the quotient by the canonical two-core. -/
theorem canonical_twoCore_quotient (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ClassicalGroup.IsPSL (XiQuotient (canonicalSupplement T L)) 2 p :=
  canonical_twoCore_quotient_of_radical_eq h hmany hL hn
    (canonical_radical_eq_twoCore h hmany hL hn)

/-- Discharge both premises of the original comparison for every actual radical supplement. -/
theorem canonical_supplement_comparison (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    canonicalSupplement T L ∈ radicalSupplements T L ∧
      (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L ∧
      ∀ B ∈ radicalSupplements T L,
        normalizerResidual B (radicalSylowCentralizer T L) = canonicalSupplement T L ∧
        (solvableRadical B).map B.subtype ⊔ canonicalSupplement T L = B ∧
        canonicalSupplement T L ≤ B ∧
        (((solvableRadical B).map B.subtype : Subgroup G) : Set G) *
          (canonicalSupplement T L : Set G) = (B : Set G) :=
  canonical_supplement_comparison_source h hmany hL hn (radical_sylow_source h hL hn)
    (canonical_quasisimple h hmany hL hn)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
