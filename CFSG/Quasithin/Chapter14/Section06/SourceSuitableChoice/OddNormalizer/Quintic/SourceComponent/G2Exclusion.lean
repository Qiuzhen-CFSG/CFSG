module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.SymplecticExclusion
public import Theory.SpecificGroups.G2.QuinticRadical

/-!
# Excluding the nonbinary G₂ star component

The actual first-factor action preserves the radical intersection on the
star component. Its full radical normalizer normalizes that action. At odd
field degree the component has order prime to five, so the actual quintic
actor has outer order five and the actor group's inner intersection is a
two-group. The intrinsic G₂ Borel-displacement obstruction excludes this
row, leaving the linear-three model with all six B.5.1 clauses retained.

The linear-three comparison, exchanged module geometry, original index
premise and final p=3 assembly remain with qt-e-14615-quintic-exclusion.
Earlier 14.6.12--14 discharge remains with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed p.1035. The original radical,
action and component isomorphism are retained throughout.
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

/-- The nonbinary G₂ star row is incompatible with the original radical
normalizer and first-factor action. -/
theorem source_no_nonbinary_g2_star (F : BinaryField) (hl : 1 < F.degree)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* Atlas.G2.Model F.Carrier) : False := by
  let R := Mc.pCoreIn 2
  let C := starImage j.J R j.J
  let Q := (starImage j.J R R).subgroupOf C
  let f := (starComponentAction j.J R).comp
    (inclusion (source_first_le_common_normalizer s d j))
  have hi := source_component_input s d j
  have hg := source_component_g2_quintic_field s d j F hl e
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact lt_of_eq_of_lt (by decide : 2=2^1) (Nat.pow_lt_pow_right (by decide) hl)
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model]
    have h4 : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hl
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left h4 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 6) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4^6*(4^6-1)*(4^2-1)) hh
  obtain ⟨hr,hN⟩ := star_intersection_placement_from_source_of_large_order hi hlarge
  have hNf : (normalizer (Q : Set C)).map MulAut.conj ≤ normalizer (f.range : Set _) := by
    have he : f.range = (d.K1.subgroupOf
        (normalizer (j.J : Set G) ⊓ normalizer (R : Set G))).map
          (starComponentAction j.J R) := by rw [MonoidHom.range_comp,inclusion_range]
    rw [he]
    exact (map_mono hN).trans (source_borel_normalizes_first_actor s d j hi.normalizes)
  obtain ⟨k,hk,_,_,ha,hout,ho⟩ := source_component_star_outer_quintic_of_rank_zero
    s d j hi.normalizes hg.2.2.1
  let y : d.K1 := ⟨k,hk⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup C)
  let o := q.comp f
  have h5 : 5 ∣ Nat.card o.range := by
    have hh := orderOf_dvd_natCard (o.rangeRestrict y)
    rw [Subgroup.orderOf_mk] at hh
    exact ho ▸ hh
  obtain ⟨_,_,⟨em⟩,_⟩ := source_normalizer_geometry_residual_models s d
  have hc : Nat.card (d.K1 ⧸ pCore 2 d.K1) = 5 := by
    rw [Nat.card_congr em.toEquiv]
    simp
  have ht : IsPGroup 2 (f.range ⊓ MulAut.innerSubgroup C : Subgroup _) :=
    MulAut.inner_intersection_isPGroup_of_outer_range f (by decide) hc h5
  have hfix : Q.map (starComponentAction j.J R k).toMonoidHom = Q :=
    source_component_radical_intersection_fixed s d j k
  exact Theory.SpecificGroups.G2Quintic.no_radical_quintic_actor_of_equiv e hq
    (Theory.SpecificGroups.Classical.QuinticRankOne.g2_five_not_dvd F.card_eq hg.1)
    Q hr f.range ht hNf _ ⟨y,rfl⟩ ha hfix

/-- After both remaining rank-two classical comparisons, only linear three remains. -/
theorem source_component_linear_row_reduction
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation j.J (Mc.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) :
    ∃ F : BinaryField, ¬4 ∣ F.degree ∧ Nonempty
      (((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) ≃* SL(3,F.Carrier)) := by
  cases source_component_linear_g2_row_reduction s d j hCJ c with
  | linearThree F hd e => exact ⟨F,hd,⟨e⟩⟩
  | g2 F hl hd h5 e =>
    exact (source_no_nonbinary_g2_star s d j F hl
      ((subgroupOfEquivOfLe hCJ).symm.trans e)).elim

/-- All six B.5.1 clauses and the last actual component model. -/
theorem source_component_linear_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (_c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))))
      (F : BinaryField), ¬4 ∣ F.degree ∧ Nonempty
        (((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) ≃* SL(3,F.Carrier)) := by
  have hi := source_component_input s d j
  have hc := star_moved_section_from_source hi
  let c := Classical.choice hc.2
  exact ⟨hc.1,c,source_component_linear_row_reduction s d j hc.1 c⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
