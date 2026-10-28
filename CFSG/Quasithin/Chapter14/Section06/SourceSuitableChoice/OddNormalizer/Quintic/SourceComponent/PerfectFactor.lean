module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.NaturalJoin
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.QuasisimpleSections
public import Theory.GroupTheory.CComponent.PerfectProjection
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoImages
public import Theory.SpecificGroups.PSL2.SixteenWreathComponents

/-!
# Containment of the exchanged perfect factor in the escaping component

The source second normalizer is SQTK, so the actual quasisimple core
quotient has solvable outer automorphism group. The perfect first factor
acts by inner automorphisms. The existing order-five action and literal
kernel calculation then force five-rank one and K₁ ≤ J K₂. The two distinct
C-components commute modulo a solvable subgroup; quotienting by the now
normal J improves this to actual containment K₁ ≤ J.

This supplies the C.2.7 input, the original point containment and the
proved natural-row exclusion. The simple quotient of K₁ also survives the
solvable star kernel. In the PSL₂(16) case its full order 4080 divides the
literal marked intersection, as required for the remaining model comparison.

The owner qt-e-14615-quintic-exclusion retains the module geometry, terminal
model comparison and p=3 assembly. No ordinary-centralizer residual identity
is used. Earlier14.6.12--14 inputs retain discharge with
qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith14.6.15, printed p.1035, using C.2.7 and A.3.6.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped commutatorElement Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
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


/-- The actual core quotient is a quasisimple section of the source second normalizer. -/
theorem source_component_core_outer_solvable :
    Group.IsSolvable (MulAut.Outer (j.J ⧸ pCore 2 j.J)) := by
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  let : IsQuasisimple (j.J ⧸ pCore 2 j.J) := j.quasisimple
  have hsec : ChapterA.Section02.IsSectionOf (j.J ⧸ pCore 2 j.J)
      (normalizer (d.K2 : Set G)) :=
    (ChapterA.Section02.IsSectionOf.of_surjective (QuotientGroup.mk' (pCore 2 j.J))
      (QuotientGroup.mk'_surjective _)).ambient_injective
      (inclusion j.component_le) (inclusion_injective _)
  exact ChapterA.Section03.SourceComponents.quasisimple_section_outer_solvable hs.sqtk hsec

/-- Every first-factor actor is inner when that factor is perfect. -/
theorem source_perfect_first_acts_inner [Group.IsPerfect d.K1]
    (k : normalizer (j.J : Set G)) (hk : (k : G) ∈ d.K1) :
    pCoreNormalizerAction 2 j.J k ∈ MulAut.innerSubgroup (j.J ⧸ pCore 2 j.J) := by
  let : Group.IsSolvable (MulAut.Outer (j.J ⧸ pCore 2 j.J)) :=
    source_component_core_outer_solvable s d j
  let hn := (source_first_le_common_normalizer s d j).trans inf_le_left
  let f := (pCoreNormalizerOuterAction 2 j.J).comp (inclusion hn)
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra! hnt
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have he : f ⟨k,hk⟩ = 1 := congrArg Subtype.val
    (hsub.elim (f.rangeRestrict ⟨k,hk⟩) 1)
  exact (QuotientGroup.eq_one_iff _).mp he

/-- Perfectness excludes the zero-five-rank component, using the literal core action. -/
theorem source_perfect_first_component_rank [Group.IsPerfect d.K1] :
    primeRank 5 j.J = 1 := by
  have hr := j.quintic_rank
  have hzero : primeRank 5 j.J ≠ 0 := by
    intro hz
    obtain ⟨k,hk,_,_,_,hout,_⟩ := source_component_outer_quintic_of_rank_zero s d j hz
    exact hout (source_perfect_first_acts_inner s d j k hk)
  omega

/-- The rank-one kernel calculation places the perfect first factor in the genuine join. -/
theorem source_perfect_first_le_join [Group.IsPerfect d.K1] :
    d.K1 ≤ j.J ⊔ d.K2 := by
  rcases component_rank_one_first_join_or_outer s d j.J j.component_le j.component
      j.quasisimple j.outside j.characteristic_component
      (source_perfect_first_component_rank s d j) with h | ⟨k,hk,_,_,_,hout,_⟩
  · exact h
  · exact (hout (source_perfect_first_acts_inner s d j k hk)).elim

/-- The two distinct component factors have solvable commutator in the original ambient group. -/
theorem source_component_factors_solvable_commutator
    (hfirst : (d.K1.subgroupOf Mc).IsCComponent)
    (hsecond : (d.K2.subgroupOf Mc).IsCComponent) :
    Group.IsSolvable (⁅d.K1,d.K2⁆ : Subgroup G) := by
  have hne : d.K1 ≠ d.K2 := by
    intro he
    obtain ⟨t,_,hnt,ht⟩ := d.exchanged
    have hm := mem_normalizer_iff_map_conj_eq.mpr (ht.trans he.symm)
    exact hnt (by simpa only [inv_inv] using inv_mem hm)
  have hne' : d.K1.subgroupOf Mc ≠ d.K2.subgroupOf Mc := by
    intro he
    apply hne
    have hh := congrArg (map Mc.subtype) he
    simpa only [map_subgroupOf_eq_of_le d.first_le,map_subgroupOf_eq_of_le d.second_le] using hh
  have hc := hfirst.commutator_le_solvableRadical_of_ne hsecond hne'
  let : Group.IsSolvable (⁅d.K1.subgroupOf Mc,d.K2.subgroupOf Mc⁆ : Subgroup Mc) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hc)
  have he : (⁅d.K1.subgroupOf Mc,d.K2.subgroupOf Mc⁆ : Subgroup Mc).map Mc.subtype =
      ⁅d.K1,d.K2⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le d.first_le,map_subgroupOf_eq_of_le d.second_le]
  rw [←he]
  exact Group.isSolvable_of_surjective (Mc.subtype.subgroupMap_surjective _)

/-- The joined placement improves to actual containment for the exchanged components.
Perfectness removes their solvable cross-commutator after quotienting by J. -/
theorem source_component_first_le_component
    (hfirst : (d.K1.subgroupOf Mc).IsCComponent)
    (hsecond : (d.K2.subgroupOf Mc).IsCComponent) : d.K1 ≤ j.J := by
  let : Group.IsPerfect (d.K1.subgroupOf Mc) := hfirst.perfect
  let : Group.IsPerfect d.K1 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe d.first_le).toMonoidHom)
    (subgroupOfEquivOfLe d.first_le).surjective
  have hr := source_perfect_first_component_rank s d j
  have hjoin := source_perfect_first_le_join s d j
  let N := normalizer (d.K2 : Set G)
  have h1N : d.K1 ≤ N := (show d.K1 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_left).trans
    (closure_le_secondNormalizer s d)
  let A := d.K1.subgroupOf N
  let B := d.K2.subgroupOf N
  let C := j.J.subgroupOf N
  let : C.Normal := j.rank_one_normal hr
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h1N).symm.toMonoidHom)
    (subgroupOfEquivOfLe h1N).symm.surjective
  let : Group.IsSolvable (⁅d.K1,d.K2⁆ : Subgroup G) :=
    source_component_factors_solvable_commutator s d hfirst hsecond
  have hmap : (⁅A,B⁆ : Subgroup N).map N.subtype = ⁅d.K1,d.K2⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le h1N,
      map_subgroupOf_eq_of_le d.K2.le_normalizer]
  let e := (⁅A,B⁆ : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective
  let : Group.IsSolvable (⁅A,B⁆ : Subgroup N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (e.trans (MulEquiv.subgroupCongr hmap)).toMonoidHom)
      (e.trans (MulEquiv.subgroupCongr hmap)).injective
  have h : A ≤ C ⊔ B := by
    rw [←subgroupOf_sup j.component_le d.K2.le_normalizer]
    exact subgroupOf_mono N hjoin
  have hAC := perfect_le_normal_of_le_sup_of_solvable_commutator A B C h
  intro x hx
  exact hAC (show (⟨x,h1N hx⟩ : N) ∈ A from hx)

/-- The actual C.2.7 comparison for the exchanged component pair now has
containment, rank one and the original point, with its natural row excluded. -/
theorem source_component_factors_contained_comparison
    (hfirst : (d.K1.subgroupOf Mc).IsCComponent)
    (hsecond : (d.K2.subgroupOf Mc).IsCComponent) :
    d.K1 ≤ j.J ∧ primeRank 5 j.J = 1 ∧ centralInvolutions T ≤ j.J ∧
      Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
        (Mc ⊓ normalizer (d.K2 : Set G)) j.J ∧
      ¬Nonempty (NaturalStarRow j.J (Mc.pCoreIn 2)) := by
  let : Group.IsPerfect (d.K1.subgroupOf Mc) := hfirst.perfect
  let : Group.IsPerfect d.K1 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe d.first_le).toMonoidHom)
    (subgroupOfEquivOfLe d.first_le).surjective
  have hcontained := source_component_first_le_component s d j hfirst hsecond
  have hr := source_perfect_first_component_rank s d j
  exact ⟨hcontained,hr,source_point_le_component_of_first_le_join s d j hr
    (source_perfect_first_le_join s d j),source_component_contained_input s d j hcontained,
    source_component_contained_natural_row_exclusion s d j hcontained⟩

/-- The simple first-factor quotient survives in the literal star intersection.
The star kernel is solvable, and hence lies in the perfect factor's two-core. -/
theorem source_component_factor_core_divides_star_intersection
    (hfirst : (d.K1.subgroupOf Mc).IsCComponent)
    (hsecond : (d.K2.subgroupOf Mc).IsCComponent)
    [IsSimpleGroup (d.K1 ⧸ pCore 2 d.K1)] :
    Nat.card (d.K1 ⧸ pCore 2 d.K1) ∣
      Nat.card (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))) := by
  have hc := source_component_first_le_component s d j hfirst hsecond
  have hi := source_component_contained_input s d j hc
  let : Group.IsPerfect (d.K1.subgroupOf Mc) := hfirst.perfect
  let : Group.IsPerfect d.K1 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe d.first_le).toMonoidHom)
    (subgroupOfEquivOfLe d.first_le).surjective
  let f := (toStarImage j.J (Mc.pCoreIn 2)).comp (inclusion hc)
  let k : f.ker →* (toStarImage j.J (Mc.pCoreIn 2)).ker :=
    { toFun := fun x => ⟨inclusion hc x.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := fun x y h =>
    Subtype.ext (inclusion_injective hc (congrArg Subtype.val h))
  let : Group.IsSolvable (toStarImage j.J (Mc.pCoreIn 2)).ker :=
    toStarImage_ker_solvable_from_source hi
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hk
  have hker := PerfectCoreTwoExtension.solvable_ker_le_core f
  let q : (d.K1 ⧸ f.ker) →* (d.K1 ⧸ pCore 2 d.K1) :=
    QuotientGroup.lift f.ker (QuotientGroup.mk' (pCore 2 d.K1)) (by
      simpa only [QuotientGroup.ker_mk'] using hker)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.K1) x
    exact ⟨QuotientGroup.mk' f.ker b,rfl⟩
  have hd := card_dvd_of_surjective q hq
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd
  let B := (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf
    (starImage j.J (Mc.pCoreIn 2) j.J)
  have h1N : d.K1 ≤ normalizer (d.K2 : Set G) :=
    (show d.K1 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_left).trans
      (closure_le_secondNormalizer s d)
  have hb : f.range ≤ B := by
    rintro _ ⟨b,rfl⟩
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel j.J (Mc.pCoreIn 2)))
      ⟨⟨d.first_le b.property,h1N b.property⟩,hc b.property⟩
  have hdiv := hd.trans (card_dvd_of_le hb)
  rwa [Nat.card_congr (subgroupOfEquivOfLe (starM_le j.J (Mc.pCoreIn 2)
    (Mc ⊓ normalizer (d.K2 : Set G)))).toEquiv] at hdiv

/-- The full order of the actual PSL₂(16) quotient survives in the marked intersection. -/
theorem source_exchanged_factor_star_intersection_order
    (hfirst : (d.K1.subgroupOf Mc).IsCComponent)
    (hsecond : (d.K2.subgroupOf Mc).IsCComponent)
    (hmodel : Nonempty ((d.K1 ⧸ pCore 2 d.K1) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    4080 ∣ Nat.card (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))) := by
  obtain ⟨e⟩ := hmodel
  let := Theory.PSL2.SixteenWreathComponents.simple
  let : IsSimpleGroup (d.K1 ⧸ pCore 2 d.K1) := e.isSimpleGroup
  have hd := source_component_factor_core_divides_star_intersection s d j hfirst hsecond
  rw [Nat.card_congr e.toEquiv] at hd
  have hc : Nat.card Theory.PSL2.SixteenWreathComponents.L = 4080 := by
    rw [←Nat.card_congr (Atlas.RankOneFieldAutomorphisms.slEquivPSL
      (F := GaloisField 2 4)).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 4 (by decide)]
    rfl
  rwa [hc] at hd

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
