module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.G2Exclusion
public import Theory.SpecificGroups.SL3.QuinticRadical

/-!
# Removing odd-degree SL₃ components in original 14.6.15

The literal first-factor action preserves the star radical intersection and
is normalized by its full normalizer. At odd field degree the component is
five-free, so its quintic actor is outer and the actor group's inner
intersection is a two-group. The intrinsic SL₃ Borel obstruction excludes
this case. The binary model is handled by its actual automorphism order.
All six B.5.1 clauses remain attached to the surviving component.

The even-degree comparison, exchanged module geometry, original index
premise and p=3 assembly remain with qt-e-14615-quintic-exclusion. Earlier
14.6.12--14 inputs retain their discharge with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed p.1035.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

theorem source_no_odd_linear_star (F : BinaryField) (ho : Odd F.degree)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* SL(3,F.Carrier)) : False := by
  by_cases he : F.degree = 1
  · obtain ⟨k,_,_,ha⟩ := source_component_star_quintic s d j
      (source_component_input s d j).normalizes
    exact Matrix.SL3.QuinticRadical.no_binary_actor F.Carrier
      (by simpa [he] using F.card_eq) e _ ha
  have hl : 1 < F.degree := by have hp := F.degree_pos; omega
  let R := Mc.pCoreIn 2
  let C := starImage j.J R j.J
  let Q := (starImage j.J R R).subgroupOf C
  let f := (starComponentAction j.J R).comp
    (inclusion (source_first_le_common_normalizer s d j))
  have hi := source_component_input s d j
  have hf : ¬5 ∣ Nat.card C := by
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.SL3.QuinticRadical.five_not_dvd F.card_eq ho
  have hzero : primeRank 5 j.J = 0 := by
    rw [←source_component_star_five_rank s d j hi.normalizes]
    exact PrimeRank.eq_zero_iff_not_dvd_card.mpr hf
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    have h4 : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hl
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left h4 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4^3*(4^3-1)*(4^2-1)) hh
  obtain ⟨hr,hN⟩ := star_intersection_placement_from_source_of_large_order hi hlarge
  have hNf : (normalizer (Q : Set C)).map MulAut.conj ≤ normalizer (f.range : Set _) := by
    have he : f.range = (d.K1.subgroupOf
        (normalizer (j.J : Set G) ⊓ normalizer (R : Set G))).map
          (starComponentAction j.J R) := by rw [MonoidHom.range_comp,inclusion_range]
    rw [he]
    exact (map_mono hN).trans (source_borel_normalizes_first_actor s d j hi.normalizes)
  obtain ⟨k,hk,_,_,ha,hout,horder⟩ := source_component_star_outer_quintic_of_rank_zero
    s d j hi.normalizes hzero
  let y : d.K1 := ⟨k,hk⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup C)
  let o := q.comp f
  have h5 : 5 ∣ Nat.card o.range := by
    have hh := orderOf_dvd_natCard (o.rangeRestrict y)
    rw [Subgroup.orderOf_mk] at hh
    exact horder ▸ hh
  obtain ⟨_,_,⟨em⟩,_⟩ := source_normalizer_geometry_residual_models s d
  have hc : Nat.card (d.K1 ⧸ pCore 2 d.K1) = 5 := by
    rw [Nat.card_congr em.toEquiv]
    simp
  have ht : IsPGroup 2 (f.range ⊓ MulAut.innerSubgroup C : Subgroup _) :=
    MulAut.inner_intersection_isPGroup_of_outer_range f (by decide) hc h5
  have hfix : Q.map (starComponentAction j.J R k).toMonoidHom = Q :=
    source_component_radical_intersection_fixed s d j k
  exact Matrix.SL3.QuinticRadical.no_radical_quintic_actor_of_equiv F.Carrier e hl F.card_eq ho
    Q hr f.range ht hNf _ ⟨y,rfl⟩ ha hfix

/-- Only degrees congruent to two modulo four remain in the actual linear-three row. -/
theorem source_component_linear_degree_mod_four (F : BinaryField)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* SL(3,F.Carrier)) :
    F.degree % 4 = 2 := by
  have hfour := source_component_linear_degree s d j F e
  have heven : Even F.degree := Nat.not_odd_iff_even.mp
    (fun ho => source_no_odd_linear_star s d j F ho e)
  have ht := even_iff_two_dvd.mp heven
  have hn : F.degree % 4 ≠ 0 := fun h => hfour (Nat.dvd_of_mod_eq_zero h)
  omega

/-- Preserve the full B.5.1 conclusion while removing every odd-degree row. -/
theorem source_component_even_linear_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (_c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))))
      (F : BinaryField), F.degree % 4 = 2 ∧ Nonempty
        (((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) ≃* SL(3,F.Carrier)) := by
  obtain ⟨hCJ,c,F,_,⟨e⟩⟩ := source_component_linear_moved_rows s d j
  exact ⟨hCJ,c,F,source_component_linear_degree_mod_four s d j F
    ((subgroupOfEquivOfLe hCJ).symm.trans e),⟨e⟩⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
