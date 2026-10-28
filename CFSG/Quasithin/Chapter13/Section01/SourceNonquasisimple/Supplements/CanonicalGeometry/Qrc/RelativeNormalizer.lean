module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Qrc.Module


/-!
# The intrinsic radical intersection determines the canonical supplement

Write S=R∩L. A radical supplement B normalizing S has a normal Sylow
two-subgroup in its radical. Thus its two-core quotient has odd radical,
and A.3.6 makes that quotient quasisimple. The proved canonical comparison
and two-core normalization then force B to be the canonical supplement.

Apply this to N_L(S)^∞. Frattini factorization makes it an actual local
radical supplement, so N_L(R)^∞=N_L(R∩L)^∞. Consequently any subgroup
normalizing L and R∩L normalizes the canonical supplement. This is the
normalizer transfer needed in case (I) of the qrc argument; establishing
normality of R∩L in the actual comparison subgroup remains with the same
13.1.9 assembly owner. No normality in all of N_G(L) is asserted.

Source: Aschbacher--Smith, 13.1.9, printed p.869, using A.3.6 and 1.2.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- A radical supplement normalizing the radical Sylow intersection is the
canonical supplement. Normality is only relative to that supplement. -/
theorem supplement_eq_canonical_of_normalizes_radical_intersection
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L B : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hB : B ∈ radicalSupplements T L)
    (hBS : B ≤ normalizer ((radicalSylowCentralizer T L ⊓ L : Subgroup G) : Set G)) :
    B = canonicalSupplement T L := by
  let S := radicalSylowCentralizer (T : Subgroup G) L ⊓ L
  let A := (solvableRadical B).map B.subtype
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hTB := (supplements_invariant_source h hmany hL hn hB).1
  have hk := (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1
  have hrad : A = B ⊓ (solvableRadical L).map L.subtype := supplement_radical hk hB.2
  have hBS' : B ≤ normalizer (((T : Subgroup G) ⊓ A : Subgroup G) : Set G) := by
    have he : (T : Subgroup G) ⊓ A = S ⊓ B := by
      dsimp only [S]
      rw [hrad, radicalSylowCentralizer_inf_component T hTL]
      ac_rfl
    rw [he]
    exact (le_inf hBS B.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hs : IsSylowIn 2 ((T : Subgroup G) ⊓ A) A := by
    let W := B ⊔ (T : Subgroup G)
    let : (A.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer
      ((sup_le B.le_normalizer hTB).trans
        (normalizer_le_normalizer_characteristic_image B (solvableRadical B)))
    exact IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
      ((map_subtype_le _).trans le_sup_left)
      (inferInstance : (A.subgroupOf W).Normal).isSubnormal
  have hcore : (T : Subgroup G) ⊓ A ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_right.trans (map_subtype_le _)) hBS'
  have hsB : IsSylowIn 2 (((T : Subgroup G) ⊓ A).subgroupOf B) (solvableRadical B) := by
    apply (IsSylowIn.map_iff B.subtype B.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (inf_le_right.trans (map_subtype_le _))]
    exact hs
  obtain ⟨P,hP⟩ := hsB
  have hPC : (P : Subgroup (solvableRadical B)) ≤
      (pCore 2 B).subgroupOf (solvableRadical B) := by
    apply map_le_iff_le_comap.mp
    rw [hP]
    apply (map_le_map_iff_of_injective B.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (inf_le_right.trans (map_subtype_le _))]
    exact hcore
  have ho : Odd (Nat.card (solvableRadical (XiQuotient B))) := by
    apply odd_radical_twoCore_quotient_iff.mpr
    exact Nat.not_even_iff_odd.mp (fun he => P.not_dvd_index
      ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hPC)))
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk h.simpleQTKE hB.1.2.2) hB.1.1
  let C := radicalLocalImage T B
  let e : XiQuotient B ≃* C := radicalLocalQuotientEquiv hB.1
  let : Group.IsPerfect (B.subgroupOf (B ⊔ (T : Subgroup G))) := hB.1.1.perfect
  let : Group.IsPerfect C := Group.IsPerfect.map _
  have hoC : Odd (Nat.card (solvableRadical C)) := by
    rw [← map_solvableRadical_equiv e]
    exact (Nat.card_congr (e.subgroupMap (solvableRadical (XiQuotient B))).toEquiv) ▸ ho
  let : IsQuasisimple C := hc.2.isQuasisimple_of_odd_radical hoC
  let : IsQuasisimple (XiQuotient B) := IsQuasisimple.of_mulEquiv e.symm
  let : Group.IsPerfect B := mem_L_isPerfect hB.1
  let Y := canonicalSupplement (T : Subgroup G) L
  have hcomp := (canonical_supplement_comparison h hmany hL hn).2.2 B hB
  have hYB : Y ≤ B := hcomp.2.2.1
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    sylow_normalizes_canonicalSupplement hTL
  have hBT : B.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hb := (pCoreIn_mono_of_normalizes le_sup_left (sup_le B.le_normalizer hTB)).trans
      (pCoreIn_le_sylow (B ⊔ (T : Subgroup G)) (T.subtype le_sup_right))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ B ⊔ (T : Subgroup G) from le_sup_right)] using hb
  have hnorm : pCore 2 B ≤ normalizer (Y.subgroupOf B : Set B) := by
    rw [← subgroupOf_normalizer_eq hYB]
    exact fun b hb => hTY (hBT (mem_map_of_mem B.subtype hb))
  have hgen : solvableRadical B ⊔ Y.subgroupOf B = ⊤ := by
    apply map_injective B.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hYB,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hcomp.2.1
  have he := congrArg (map B.subtype)
    (eq_top_of_radical_supplement_of_quasisimple_quotient (pCore 2 B)
      (Y.subgroupOf B) hnorm hgen)
  simpa only [map_subgroupOf_eq_of_le hYB, ← MonoidHom.range_eq_map, range_subtype]
    using he.symm

/-- The residual normalizer of R∩L is an actual radical supplement. -/
theorem radical_intersection_normalizer_mem_supplements
    (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    normalizerResidual L (radicalSylowCentralizer T L ⊓ L) ∈ radicalSupplements T L := by
  let S := radicalSylowCentralizer (T : Subgroup G) L ⊓ L
  let W := L ⊔ (T : Subgroup G)
  let D := (solvableRadical L).map L.subtype
  let N := W ⊓ normalizer (S : Set G)
  let Z := normalizerResidual L S
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (le_inf (sylow_normalizes_radicalSylowCentralizer hTL) hTL).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ N := le_inf le_sup_right hTS
  have hSD : S ≤ D := (radicalSylowCentralizer_inf_component T hTL).le.trans inf_le_right
  have hWD : W ≤ normalizer (D : Set G) :=
    (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  have hLS : ⁅L,S⁆ ≤ D := (commutator_mono le_rfl hSD).trans
    (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hWD))
  have hs : IsSylowIn 2 S (D ⊔ S) := by
    rw [sup_eq_left.mpr hSD]
    exact radicalSylowCentralizer_inf_component_isSylow T hTL
  let : Group.IsPerfect L := mem_L_isPerfect hL.1.1
  have hgen : D ⊔ Z = L := radical_normalizerResidual_frattini
    (inf_le_right.trans L.le_normalizer) hLS hs
  have hZN : Z ≤ N := le_inf ((normalizerResidual_le _ _).trans le_sup_left)
    (normalizerResidual_le_normalizer _ _)
  have hDN : D ⊔ N = W := by
    apply le_antisymm (sup_le ((map_subtype_le _).trans le_sup_left) inf_le_left)
    apply sup_le
    · exact hgen.ge.trans (sup_le le_sup_left (hZN.trans le_sup_right))
    · exact hTN.trans le_sup_right
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (L.subtype.subgroupMap_surjective (solvableRadical L))
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hresW : solvableResidual W = L.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [map_subgroupOf_eq_of_le le_sup_left]
    exact map_residual_sup_eq_of_perfect_of_solvable L (T : Subgroup G) hTL
  have hcW : (solvableResidual W).IsCComponent := hresW.symm ▸ hL.1.1.1
  have hcN := residual_isCComponent_of_solvable_supplement_in W D N
    ((map_subtype_le _).trans le_sup_left) inf_le_left hWD hDN hcW
  have hresN : Z.subgroupOf N = solvableResidual N := by
    change (normalizerResidual L S).subgroupOf N = solvableResidual N
    rw [← localNormalizer_residual_eq L (T : Subgroup G) S hL.1.1.2.1 hTL]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  have hQT : W.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow W (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ W from le_sup_right)] using hh
  have hQN : W.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 W) (hQT.trans hTN)
      (inf_le_left.trans (W.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image W (pCore 2 W))))
  have hNlocal : N ∈ Chapter1.H G := by
    intro hz
    exact hL.1.1.2.2 (eq_bot_iff.mpr (hQN.trans_eq hz))
  exact ⟨mem_L_of_cComponent hNlocal (hL.1.1.2.1.restrict hTN inf_le_left)
    hZN (hresN.symm ▸ hcN), hgen⟩

/-- The canonical residual may be computed using the intersection R∩L.
This is an equality of solvable residuals, not of the whole normalizers. -/
theorem canonical_eq_intersection_normalizerResidual
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    canonicalSupplement T L = normalizerResidual L (radicalSylowCentralizer T L ⊓ L) := by
  exact (supplement_eq_canonical_of_normalizes_radical_intersection h hmany hL hn
    (radical_intersection_normalizer_mem_supplements h hL hn)
    (normalizerResidual_le_normalizer _ _)).symm

/-- Normalizing L and its radical Sylow intersection normalizes the
canonical supplement; no normality in the full N_G(L) is assumed. -/
theorem normalizes_canonical_of_normalizes_radical_intersection
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hAL : A ≤ normalizer (L : Set G))
    (hAS : A ≤ normalizer ((radicalSylowCentralizer T L ⊓ L : Subgroup G) : Set G)) :
    A ≤ normalizer (canonicalSupplement T L : Set G) := by
  rw [canonical_eq_intersection_normalizerResidual h hmany hL hn]
  exact le_normalizer_normalizerResidual hAL hAS

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
