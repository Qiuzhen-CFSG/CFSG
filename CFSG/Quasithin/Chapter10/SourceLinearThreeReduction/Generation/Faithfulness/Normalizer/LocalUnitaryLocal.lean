module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBounds
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalFiniteExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBinaryExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.QuotientGeometry
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectPairLocals
public import Theory.GroupTheory.TwoLocalTransport

/-!
# Unitary component exclusions for the original nonnormal pair

The literal fixed residual in the central quotient of a containing component
is perfect, retains twice every odd rank of L/O₂(L), and normalizes the
nontrivial moved binary module. Unitary-four parabolics have odd rank at
most one on perfect subgroups. For PSU₅(4), Burnside's two-prime obstruction
handles the two parabolic types without an A₅ marking.

Source: Aschbacher--Smith 4.4.12, printed p.622, used in 10.2.3(2), p.745.
Residual placement and module fixation remain explicit earlier premises.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every positive binary unitary-four row contradicts the placed original residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_unitary_four_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {a : ℕ} (ha : 0 < a) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ a)) :
    False := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := (F.subgroupOf K).map (QuotientGroup.mk' (center K))
  let W := ((V.subgroupOf N).subgroupOf K).map (QuotientGroup.mk' (center K))
  obtain ⟨hP,hW,hE,_,hPW,hr⟩ :=
    source_local_oddActor_component_quotient_geometry
      D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  let : IsElementaryAbelian 2 W := hE
  let M := normalizer (W : Set (K ⧸ center K))
  have hM : IsTwoLocal M := ⟨W,hW,IsElementaryAbelian.isPGroup 2 W,rfl⟩
  obtain ⟨E,hEfield,hEfin,J,hcard,hconj,⟨j⟩⟩ := hm
  let : CharP E 2 := UnitaryFourFormTransport.charP_two a ha hcard
  obtain ⟨j0⟩ := UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J a ha hcard hconj
  let t := j.trans j0
  let f := t.toMonoidHom.comp P.subtype
  have hf : Function.Injective f := t.injective.comp P.subtype_injective
  have hl : f.range ≤ M.map t.toMonoidHom := by
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hPW x.property)
  obtain ⟨p,hp,ho,hdiv⟩ := source_component_quotient_has_odd_prime D
  let : Fact p.Prime := ⟨hp⟩
  have hpos : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
    fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hdiv
  have hpair := hr p hp ho
  change primeRank p P = 2 * primeRank p (L ⧸ pCore 2 L) at hpair
  have hb := UnitaryFourConverse.PerfectSubgroups.perfect_twoLocal_odd_primeRank_le_one
    J.conj J.conj_involutive a ha hcard hconj (p := p) ho
    f hf (M.map t.toMonoidHom) (Theory.GroupTheory.isTwoLocal_map t hM) hl
  omega

/-- The unitary-five-four row contradicts the actual two-factor odd ranks,
without assuming that the original component has primes three and five. -/
theorem source_nonnormal_oddNormalizer_no_placed_unitary_five_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) : False := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := (F.subgroupOf K).map (QuotientGroup.mk' (center K))
  let W := ((V.subgroupOf N).subgroupOf K).map (QuotientGroup.mk' (center K))
  obtain ⟨hP,hW,hE,_,hPW,hr⟩ :=
    source_local_oddActor_component_quotient_geometry
      D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  let : IsElementaryAbelian 2 W := hE
  let M := normalizer (W : Set (K ⧸ center K))
  have hM : IsTwoLocal M := ⟨W,hW,IsElementaryAbelian.isPGroup 2 W,rfl⟩
  obtain ⟨E,hEfield,hEfin,J,hcard,hconj,⟨j⟩⟩ := hm
  have hc : Nat.card E = 16 := by simpa using hcard
  let : CharP E 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hc
  obtain ⟨j0⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hc hconj
  let t := j.trans j0
  let f := t.toMonoidHom.comp P.subtype
  have hf : Function.Injective f := t.injective.comp P.subtype_injective
  have hl : f.range ≤ M.map t.toMonoidHom := by
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hPW x.property)
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  apply Theory.SpecificGroups.UnitaryFive.PerfectLocals.no_perfect_doubled_odd_ranks_in_twoLocal
    (HermitianForm.IdentityGram.identityGram J) hc hconj rfl S f hf
    (fun p hp ho => (hr p hp ho).ge) (M.map t.toMonoidHom)
    (Theory.GroupTheory.isTwoLocal_map t hM) hl
end CFSG.Quasithin.Chapter10.LocalFixed
