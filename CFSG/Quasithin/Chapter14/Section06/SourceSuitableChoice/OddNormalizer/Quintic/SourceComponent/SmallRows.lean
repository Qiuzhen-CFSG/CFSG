module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.RadicalNormalization
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixThompson
public import Theory.SpecificGroups.QuinticTwoLocal

/-!
# Small generated rows in the quintic component comparison

The actual Thompson image is nontrivial. When the source moved-section
row places it in the component, its radical intersection is a nontrivial
two-subgroup preserved by the literal first-factor automorphisms. An
order-five actor therefore excludes the small alternating models, their
odd central covers, and the binary linear-four model. Ratio-one generated
rows and whole-component rows supply the Thompson containment themselves.

These are actual model exclusions for the extracted component. The other
rows, exchanged module geometry and final p=3 assembly remain with
qt-e-14615-quintic-exclusion. The earlier 14.6.12--14 inputs retain discharge
with qt-e-suitable-odd-normalizer. No ordinary-centralizer identity is used.
Source: Aschbacher--Smith 14.6.15, p.1035, using B.5.1 and C.2.7.
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

/-- The literal radical intersection is nontrivial and preserved by all
common normalizers once the actual Thompson image lies in the component. -/
theorem source_component_invariant_two_subgroup
    (hinner : starImage j.J (Mc.pCoreIn 2) (elementaryAbelianMaxJ (Mc.pCoreIn 2)) ≤
      starImage j.J (Mc.pCoreIn 2) j.J) :
    ∃ Q : Subgroup (starImage j.J (Mc.pCoreIn 2) j.J),
      IsPGroup 2 Q ∧ Q ≠ ⊥ ∧
      ∀ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
        Q.map (starComponentAction j.J (Mc.pCoreIn 2) k).toMonoidHom = Q := by
  have hi := source_component_input s d j
  let R := Mc.pCoreIn 2
  let C := starImage j.J R j.J
  let Q := (R.subgroupOf j.J).map (toStarImage j.J R)
  let : (j.J.subgroupOf (j.J ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le j.J.le_normalizer hi.normalizes)
  have hne : Q ≠ ⊥ := by
    rw [show Q = (starImage j.J R R).subgroupOf C from
      component_intersection_star_eq_of_normal_input (source_join_input hi)]
    exact (star_intersection_radical_of_thompson_inner (source_join_input hi) hinner).1
  refine ⟨Q,(isPGroup_pCoreIn 2 Mc).comap_subtype.map _,hne,?_⟩
  intro k
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    change starComponentAction j.J R k (toStarImage j.J R x) ∈ Q
    rw [starComponentAction_apply,starComponentAut_toStarImage]
    apply mem_map_of_mem
    change (k : G) * (x : G) * (k : G)⁻¹ ∈ R
    exact (mem_normalizer_iff.mp k.property.2 x).mp hx
  · exact (Nat.card_congr
      ((starComponentAction j.J R k).subgroupMap Q).toEquiv).le

/-- Small alternating star models cannot carry the original quintic actor
and an inner Thompson image. -/
theorem source_no_small_alternating_star
    (hinner : starImage j.J (Mc.pCoreIn 2) (elementaryAbelianMaxJ (Mc.pCoreIn 2)) ≤
      starImage j.J (Mc.pCoreIn 2) j.J)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨Q,hQ,hne,hfix⟩ := source_component_invariant_two_subgroup s d j hinner
  obtain ⟨k,_,_,ha⟩ := source_component_star_quintic s d j
    (source_component_input s d j).normalizes
  exact Theory.SpecificGroups.QuinticTwoLocal.no_order_five_alternating
    hn e Q hQ hne _ ha (hfix k)

/-- The odd central kernel of a small alternating cover is retained. -/
theorem source_no_small_central_alternating_star
    (hinner : starImage j.J (Mc.pCoreIn 2) (elementaryAbelianMaxJ (Mc.pCoreIn 2)) ≤
      starImage j.J (Mc.pCoreIn 2) j.J)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : ((starImage j.J (Mc.pCoreIn 2) j.J) ⧸
      center (starImage j.J (Mc.pCoreIn 2) j.J)) ≃* alternatingGroup (Fin n))
    (hz : Nat.Coprime 2 (Nat.card (center (starImage j.J (Mc.pCoreIn 2) j.J)))) : False := by
  have hi := source_component_input s d j
  let : IsQuasisimple (j.J ⧸ pCore 2 j.J) := j.quasisimple
  let : Group.IsPerfect (starImage j.J (Mc.pCoreIn 2) j.J) :=
    Group.IsPerfect.ofSurjective (coreToStar_surjective hi.normalizes)
  obtain ⟨Q,hQ,hne,hfix⟩ := source_component_invariant_two_subgroup s d j hinner
  obtain ⟨k,_,_,ha⟩ := source_component_star_quintic s d j hi.normalizes
  exact Theory.SpecificGroups.QuinticTwoLocal.no_order_five_central_alternating
    hn e hz Q hQ hne _ ha (hfix k)

/-- The binary linear-four star model has the same invariant-subgroup obstruction. -/
theorem source_no_linear_four_star
    (hinner : starImage j.J (Mc.pCoreIn 2) (elementaryAbelianMaxJ (Mc.pCoreIn 2)) ≤
      starImage j.J (Mc.pCoreIn 2) j.J)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* SL(4,ZMod 2)) : False := by
  obtain ⟨Q,hQ,hne,hfix⟩ := source_component_invariant_two_subgroup s d j hinner
  obtain ⟨k,_,_,ha⟩ := source_component_star_quintic s d j
    (source_component_input s d j).normalizes
  exact Theory.SpecificGroups.QuinticTwoLocal.no_order_five_linear_four
    e Q hQ hne _ ha (hfix k)

variable
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (r : MovedSection ((starRepresentation j.J (Mc.pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))))

include hCJ in
/-- Ratio-one generated rows supply Thompson containment, rather than
assuming it as an additional component-comparison premise. -/
theorem source_ratio_one_thompson_inner
    (hgen : offenderSubgroup r.action =
      (starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))
    (hratio : quadraticRatio r.action = 1) :
    starImage j.J (Mc.pCoreIn 2) (elementaryAbelianMaxJ (Mc.pCoreIn 2)) ≤
      starImage j.J (Mc.pCoreIn 2) j.J := by
  have hi := source_component_input s d j
  rw [←ratio_one_component_eq_offender hi hCJ r hgen hratio]
  exact star_thompson_le_offenderSubgroup_from_source hi

include hCJ in
/-- This discharges the generated A₆-natural, A₇-four-dimensional and
A₈-orthogonal rows of the literal B.5 moved-section conclusion. -/
theorem source_no_small_alternating_ratio_one_row
    (hgen : offenderSubgroup r.action =
      (starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))
    (hratio : quadraticRatio r.action = 1)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
      (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) ≃*
        alternatingGroup (Fin n)) : False :=
  source_no_small_alternating_star s d j
    (source_ratio_one_thompson_inner s d j hCJ r hgen hratio) hn
    ((subgroupOfEquivOfLe hCJ).symm.trans e)

include hCJ in
/-- The actual triple-A₆ row is excluded through its center quotient;
no identification of the cover itself with A₆ is used. -/
theorem source_no_triple_six_ratio_one_row
    (hgen : offenderSubgroup r.action =
      (starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))
    (hratio : quadraticRatio r.action = 1)
    (a6 : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction r.action
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) : False := by
  let e := (subgroupOfEquivOfLe hCJ).symm
  apply source_no_small_central_alternating_star s d j
    (source_ratio_one_thompson_inner s d j hCJ r hgen hratio)
    (Or.inr (Or.inl rfl))
    ((QuotientGroup.congr _ _ e (map_center_equiv e)).trans a6.quotientEquiv)
  rw [Nat.card_congr (centerCongr e).toEquiv,Nat.card_congr a6.centerEquiv.toEquiv]
  norm_num

/-- A whole-component row supplies Thompson containment without a ratio
hypothesis; this is used by the binary natural-plus-dual and repeated rows. -/
theorem source_whole_row_thompson_inner
    (hwhole : (starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
      (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))) = ⊤) :
    starImage j.J (Mc.pCoreIn 2) (elementaryAbelianMaxJ (Mc.pCoreIn 2)) ≤
      starImage j.J (Mc.pCoreIn 2) j.J :=
  (star_thompson_le_offenderSubgroup_from_source (source_component_input s d j)).trans
    (subgroupOf_eq_top.mp hwhole)

include hCJ in
/-- The binary degree-four whole-component rows cannot occur. -/
theorem source_no_whole_linear_four_row
    (hwhole : (starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
      (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))) = ⊤)
    (e : ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
      (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) ≃* SL(4,ZMod 2)) : False :=
  source_no_linear_four_star s d j (source_whole_row_thompson_inner s d j hwhole)
    ((subgroupOfEquivOfLe hCJ).symm.trans e)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
