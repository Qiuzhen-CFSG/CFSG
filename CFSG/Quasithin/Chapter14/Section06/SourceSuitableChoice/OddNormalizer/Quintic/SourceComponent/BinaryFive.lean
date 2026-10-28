module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.ClassicalRows
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.PerfectFactorExclusion
public import Theory.SpecificGroups.BinaryLinear.QuinticNormalizer

/-!
# Excluding every binary-five moved-section model

The perfect exchanged factor is already impossible under the same normalizer
geometry. Thus the actual first factor is the original two-residual with
cyclic-five core quotient; it is solvable and two-perfect. Its action on an
SL₅(2) star component is inner, since that model's outer group is a two-group.
The literal radical intersection is nontrivial and its full normalizer lies
in the original marked intersection. This normalizer also normalizes the
first-factor image. The binary-five normalizer theorem gives a contradiction.

The reduction excludes the natural, repeated, natural-plus-dual and exterior
binary-five rows together, preserving the full B.5.1 source conclusion.
The remaining classical and marked small outer rows, exchanged module geometry
and final p=3 assembly remain with qt-e-14615-quintic-exclusion. Earlier
14.6.12--14 discharge stays with qt-e-suitable-odd-normalizer. No ordinary
centralizer identity is assumed.
Source: Aschbacher--Smith 14.6.15, printed p.1035, using C.2.7 and B.5.1.
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


/-- The exchanged perfect alternative is already excluded, so the actual
first factor is a solvable group with two-core quotient of order five. -/
theorem source_first_factor_solvable : Group.IsSolvable d.K1 := by
  obtain ⟨_,_,⟨e⟩,_⟩ := source_normalizer_geometry_residual_models s d
  have hc : Nat.card (d.K1 ⧸ pCore 2 d.K1) = 5 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Group.IsNilpotent (pCore 2 d.K1) := (pCore_isPGroup (p := 2) (G := d.K1)).isNilpotent
  have hp : IsPGroup 5 (d.K1 ⧸ pCore 2 d.K1) := IsPGroup.of_card (n := 1) (by simpa using hc)
  let : Group.IsNilpotent (d.K1 ⧸ pCore 2 d.K1) := hp.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 d.K1)).mpr ⟨inferInstance,inferInstance⟩

/-- Two-perfectness of the original residual eliminates every two-group
outer image, on the literal first-factor star action. -/
theorem source_first_star_inner_of_outer_two
    (ho : IsPGroup 2 (MulAut.Outer (starImage j.J (Mc.pCoreIn 2) j.J))) :
    ((starComponentAction j.J (Mc.pCoreIn 2)).comp
      (inclusion (source_first_le_common_normalizer s d j))).range ≤
        MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) := by
  have hm := source_normalizer_geometry_residual_models s d
  have hp : IsPPerfect 2 d.K1 := by
    rw [hm.1]
    exact isPPerfect_embedded_pResidual 2 H1
  let f := (starComponentAction j.J (Mc.pCoreIn 2)).comp
    (inclusion (source_first_le_common_normalizer s d j))
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
  have he := hp.hom_eq_one_of_isPGroup ho (q.comp f)
  rintro _ ⟨x,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun he x

/-- Common normalizers preserve the actual intersection of the radical
with the star component, including when that intersection is trivial. -/
theorem source_component_radical_intersection_fixed
    (k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G)) :
    ((starImage j.J (Mc.pCoreIn 2) (Mc.pCoreIn 2)).subgroupOf
      (starImage j.J (Mc.pCoreIn 2) j.J)).map
      (starComponentAction j.J (Mc.pCoreIn 2) k).toMonoidHom =
      (starImage j.J (Mc.pCoreIn 2) (Mc.pCoreIn 2)).subgroupOf
        (starImage j.J (Mc.pCoreIn 2) j.J) := by
  have hi := source_component_input s d j
  let R := Mc.pCoreIn 2
  let : (j.J.subgroupOf (j.J ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le j.J.le_normalizer hi.normalizes)
  rw [←component_intersection_star_eq_of_normal_input (source_join_input hi)]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    change starComponentAction j.J R k (toStarImage j.J R x) ∈ _
    rw [starComponentAction_apply,starComponentAut_toStarImage]
    apply mem_map_of_mem
    change (k : G) * (x : G) * (k : G)⁻¹ ∈ R
    exact (mem_normalizer_iff.mp k.property.2 x).mp hx
  · exact (Nat.card_congr
      ((starComponentAction j.J R k).subgroupMap _).toEquiv).le

private theorem linear_five_large : 40320 < Nat.card SL(5,ZMod 2) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 5).toEquiv,
    ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 5).toEquiv]
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- The binary-five component row is impossible. Its literal radical
intersection supplies the invariant subgroup; its full normalizer normalizes
the actual solvable first-factor image, contradicting the model theorem. -/
theorem source_no_binary_five_star
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* SL(5,ZMod 2)) : False := by
  have hi := source_component_input s d j
  let C := starImage j.J (Mc.pCoreIn 2) j.J
  let Q := (starImage j.J (Mc.pCoreIn 2) (Mc.pCoreIn 2)).subgroupOf C
  let f := (starComponentAction j.J (Mc.pCoreIn 2)).comp
    (inclusion (source_first_le_common_normalizer s d j))
  let : Group.IsSolvable d.K1 := source_first_factor_solvable s d
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv]
    exact linear_five_large
  obtain ⟨hQ,hN⟩ := star_intersection_placement_from_source_of_large_order hi hlarge
  have ho : IsPGroup 2 (MulAut.Outer C) :=
    (Theory.SpecificGroups.BinaryComponentResidual.linear_outer_two (Or.inr rfl)).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  have hB := source_borel_normalizes_first_actor s d j hi.normalizes
  have hfr : f.range = (d.K1.subgroupOf
      (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G))).map
        (starComponentAction j.J (Mc.pCoreIn 2)) := by
    rw [MonoidHom.range_comp,inclusion_range]
  rw [←hfr] at hB
  apply BinaryLinear.QuinticNormalizer.no_solvable_inner_actor e Q hQ.isPGroup hQ.1
    f.range (source_first_star_inner_of_outer_two s d j ho)
  · rintro _ ⟨x,rfl⟩
    exact source_component_radical_intersection_fixed s d j
      (inclusion (source_first_le_common_normalizer s d j) x)
  · exact (map_mono hN).trans hB
  · obtain ⟨k,hk,_,ha⟩ := source_component_star_quintic s d j hi.normalizes
    let y : d.K1 := ⟨k,hk⟩
    have he : f y = starComponentAction j.J (Mc.pCoreIn 2) k := rfl
    have hh := orderOf_dvd_natCard (f.rangeRestrict y)
    rw [Subgroup.orderOf_mk] at hh
    change orderOf (f y) ∣ Nat.card f.range at hh
    rwa [he,ha] at hh

/-- Remaining models after excluding every binary-five moved action. -/
inductive NonBinaryQuinticRow {D : Type*} [Group D]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop
  | linearThree (F : BinaryField) (degree : ¬4 ∣ F.degree) (e : L ≃* SL(3,F.Carrier))
  | symplectic (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | symplecticTwo (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
      (symplecticNatural (k := ZMod 2) 2)
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
  | g2 (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (field_five : 5 ∣ F.degree) (e : L ≃* Atlas.G2.Model F.Carrier)
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7 ∨ n = 8)
      (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
        (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))

private theorem nonbinary_rows {D : Type*} [Group D]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (h : ClassicalQuinticRow ρ L) (hfive : (L ≃* SL(5,ZMod 2)) → False) :
    NonBinaryQuinticRow ρ L := by
  cases h with
  | linearThree F hd e => exact .linearThree F hd e
  | symplectic F hl hd e => exact .symplectic F hl hd e
  | symplecticTwo e => exact .symplecticTwo e
  | g2 F hl hd hf e => exact .g2 F hl hd hf e
  | symmetric n hn e => exact .symmetric n hn e
  | binaryFive e => exact (hfive e).elim

/-- Remove every binary-five action, including the natural-plus-dual,
repeated natural and exterior-square alternatives, on the same moved section. -/
theorem source_component_nonbinary_row_reduction
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation j.J (Mc.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) :
    NonBinaryQuinticRow c.sectionData.action
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  apply nonbinary_rows _ _ (source_component_classical_row_reduction s d j hCJ c)
  intro e
  exact source_no_binary_five_star s d j ((subgroupOfEquivOfLe hCJ).symm.trans e)

/-- The extracted component supplies the full six-clause source conclusion
with all binary-five models excluded, without a row-selection hypothesis. -/
theorem source_component_nonbinary_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
      NonBinaryQuinticRow c.sectionData.action
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  have hi := source_component_input s d j
  have hc := star_moved_section_from_source hi
  let c := Classical.choice hc.2
  exact ⟨hc.1,c,source_component_nonbinary_row_reduction s d j hc.1 c⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
