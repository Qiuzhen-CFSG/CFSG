module

public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryAction
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryExponent
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedAction
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedDetection
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.GuardedRatio
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.PositiveStar.PositiveRadical
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source
public import Theory.GroupTheory.SolvableRadical.PrimaryDetection

/-!
# The maximal-local radical argument from canonical starred membership

For an actual maximal nonquasisimple local component, the exponent-p
primary radical is its canonical radical. A larger exponent forces p>5;
the original irreducible Frattini action and the completed guarded cubic
bound instead force p=3 or5. Thus every odd-primary residual acts trivially
on the reduced module in any overgroup in which the component is normal.
Primary detection then gives centralization by the whole solvable radical.

Only the canonical starred-membership input of source 1.3.8 remains.
The source 3.1.8 bound is proved and its standing guard follows from the
actual multiple-overgroup hypothesis. No universal A.3.12 or C.2.7 family
is assumed. In particular this is a reduction of maximal-local 3.2.14,
not its unconditional completion.

The proof adapts the generic primary argument from
Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar.PrimaryRadicals,
retaining all higher homocyclic exponents and literal ambient inclusions.
Source: Aschbacher--Smith, 3.2.14, printed p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
open Chapter1 Chapter1.Section02 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The precise canonical-radical input of 1.3.8 needed for a fixed J.
This records membership in the existing family, not centralization. -/
@[expose] def CanonicalRadicalsStarred (T : Sylow 2 G) (J : Subgroup G) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Odd p →
    p ∣ Nat.card (fittingSubgroup (XiQuotient J)) → XiP p J ∈ XiStar G (T : Subgroup G)

/-- Each original odd-primary radical of a maximal nonquasisimple local
component has zero intrinsic module. The original action and its Sylow
centralizer have no remaining premises. -/
theorem primary_intrinsicModule_eq_bot_of_stars
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hstars : CanonicalRadicalsStarred T L) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    intrinsicSignalizerModule (primaryRadical p L) = ⊥ := by
  by_cases hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))
  swap
  · have he := primaryRadical_eq_bot_of_not_dvd hG T hL.1 ho hd
    exact bot_unique ((intrinsicModule_le_self _).trans_eq he)
  have hstar : XiP p L ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T :=
    ⟨Chapter13.Section01.XiP_mem_XiPlus_source hG T hL.1 hn ho hd,
      hstars p ho hd⟩
  have h318 := source_guardedTheorem318One hG
  have hout := hasMaximalOutside_of_many T hmany
  obtain ⟨hq,he,hm⟩ := Chapter13.Section01.RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd
  have hXI := XiP_le_primaryRadical L hq
  by_cases hexp : ∀ x : primaryRadical p L ⧸ pCore 2 (primaryRadical p L), x ^ p = 1
  · have heq := le_antisymm (primaryRadical_le_XiP_of_exponent hG T hL.1 ho hexp) hXI
    rw [heq]
    exact Chapter13.Section01.GuardedPositiveStar.positive_star_intrinsicModule_eq_bot hG h318 T hout hstar
  by_contra hnonzero
  have hnorm : normalizer (XiP p L : Set G) ≤ normalizer (primaryRadical p L : Set G) := by
    rw [he]
    exact normalizer_le_normalizer_primaryRadical L p
  have hT : (T : Subgroup G) ≤ normalizer (primaryRadical p L : Set G) :=
    hstar.2.1.invariant.trans hnorm
  have hI := primaryRadical_twoPerfect L ho
  have hquot := primaryRadical_quotient_isPGroup hG T hL.1 ho
  have hirr := primaryRadical_irreducible hG T hL.1 hn ho hd hT
  have hne := reduced_action_ne_bot_of_intrinsic_module (T : Subgroup G)
    (primaryRadical p L) hT hI ho hquot hnonzero
  have hc := reduced_sylow_centralizer T (primaryRadical p L) hT hI hirr hne
  have hIM : primaryRadical p L ≤ normalizer (XiP p L : Set G) := by
    rw [he]
    exact (map_subtype_le _).trans L.le_normalizer
  have hsmall := prime_restriction_of_guarded_star hG T h318 hstar.2 hXI hIM hnorm hI
    (hout _ (he.symm ▸ hm) hstar.2.1.invariant) ho hquot
    (reducedTwoSubgroup (primaryRadical p L ⊔ (T : Subgroup G) : Subgroup G))
    isPReduced_reducedPSubgroup hc
  have hp := (primaryRadical_higher_structure hG T hL.1 hn ho hexp).1
  rcases hsmall with he | he <;> omega

/-- Every primary radical centralizes R₂ of any original overgroup in
which its defining local component is normal. -/
theorem primary_centralizes_reduced_of_stars
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hstars : CanonicalRadicalsStarred T L) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (J : Subgroup G) (hLJ : L ≤ J) (hJn : J ≤ normalizer (L : Set G)) :
    primaryRadical p L ≤ centralizer ((reducedTwoSubgroup J).map J.subtype : Set G) := by
  have hzero := primary_intrinsicModule_eq_bot_of_stars hG T hmany hL hn hstars ho
  have hXJ : primaryRadical p L ≤ J := (map_subtype_le _).trans hLJ
  have hnorm : ((primaryRadical p L).subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer
      (hJn.trans (normalizer_le_normalizer_primaryRadical L p))
  have hm : ⁅reducedTwoSubgroup J,(primaryRadical p L).subgroupOf J⁆ = ⊥ := by
    by_contra hne
    exact (intrinsicModule_ne_bot_of_reduced_action _ J hXJ hnorm.isSubnormal
      (primaryRadical_twoPerfect L ho) hne) hzero
  have ha := congrArg (Subgroup.map J.subtype) hm
  rw [map_commutator,map_subgroupOf_eq_of_le hXJ,Subgroup.map_bot,commutator_comm] at ha
  exact commutator_eq_bot_iff_le_centralizer.mp ha

/-- The primary residuals detect the whole solvable radical, proving the
maximal-component case of original 3.2.14 in every normal overgroup. -/
theorem maximal_solvableRadical_centralizes_reduced_of_stars
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hstars : CanonicalRadicalsStarred T L)
    (J : Subgroup G) (hLJ : L ≤ J) (hJn : J ≤ normalizer (L : Set G)) :
    (solvableRadical L).map L.subtype ≤
      centralizer ((reducedTwoSubgroup J).map J.subtype : Set G) := by
  let R := (solvableRadical L).map L.subtype
  have hRJ : R ≤ J := (map_subtype_le _).trans hLJ
  let N := R.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hJn.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L)))
  have hNC : N ≤ centralizer (reducedTwoSubgroup J : Set J) := by
    apply normal_centralizes_reduced_of_primary_residuals N _ isPReduced_reducedPSubgroup
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    have hc := primary_centralizes_reduced_of_stars hG T hmany hL hn hstars ho J hLJ hJn
    have he : ((primeToResidual p N).map N.subtype).map J.subtype = primaryRadical p L := by
      rw [map_embedded_primeToResidual_of_hom,
        map_subgroupOf_eq_of_le hRJ,← map_embedded_primeToResidual_of_hom p (solvableRadical L) L.subtype]
      rfl
    intro x hx
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := mem_centralizer_iff.mp (hc (he ▸ mem_map_of_mem J.subtype hx))
      (v : G) (mem_map_of_mem J.subtype hv)
    exact Subtype.ext hh
  intro r hr
  apply mem_centralizer_iff.mpr
  rintro v ⟨w,hw,rfl⟩
  exact congrArg Subtype.val
    (mem_centralizer_iff.mp (hNC (show (⟨r,hRJ hr⟩ : J) ∈ N from hr)) w hw)


/-- The literal maximal-local 3.2.14 implication for JT. The separate
canonical starred-membership producer must discharge hstars. -/
theorem maximal_solvableRadical_centralizes_sylowJoin_of_stars
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {J : Subgroup G} (hJ : J ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient J)) (hstars : CanonicalRadicalsStarred T J) :
    (solvableRadical J).map J.subtype ≤
      centralizer ((reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G)).map
        (J ⊔ (T : Subgroup G)).subtype : Set G) := by
  have hT := radicalLocal_invariant_source hJ.1
    (uniqueness_local_quotient_sqtk hG hJ.1.2.2) hn
  exact maximal_solvableRadical_centralizes_reduced_of_stars hG T hmany hJ hn hstars
    (J ⊔ (T : Subgroup G)) le_sup_left (sup_le J.le_normalizer hT)

end CFSG.Quasithin.Chapter3.RadicalCentralization
