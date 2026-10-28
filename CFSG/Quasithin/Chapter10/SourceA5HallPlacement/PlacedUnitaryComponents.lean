module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals
public import Theory.GroupTheory.TwoLocalTransport
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentQuotientMarking

/-!
# Excluding the binary unitary-four and unitary-five Hall component models

The literal residual image in the component's central quotient is perfect,
has both odd ranks equal to two, and normalizes the nontrivial moved binary
image. Its actual two-local therefore contradicts the unitary-four rank-one
parabolic bounds or the unitary-five line-three/plane-five bounds.

Source: Aschbacher--Smith 4.4.12, printed p.622. Residual placement is retained
explicitly for the source assembly; no C.2.8 or ambient SQTK input is added.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every positive binary unitary-four row contradicts the placed original residual. -/
theorem source_a5_oddNormalizer_component_not_binary_unitary_four_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
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
  let W := ((D.fullModule.subgroupOf N).subgroupOf K).map (QuotientGroup.mk' (center K))
  obtain ⟨hP,hW,hE,_,hPW,h3,h5⟩ :=
    source_a5_oddNormalizer_component_quotient_local_marking_of_residual_le
      D e hn B hBC hodd hBV K hFK
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
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hb := UnitaryFourConverse.PerfectSubgroups.perfect_twoLocal_odd_primeRank_le_one
    J.conj J.conj_involutive a ha hcard hconj (p := 3) (by decide : Odd 3)
    f hf (M.map t.toMonoidHom) (Theory.GroupTheory.isTwoLocal_map t hM) hl
  change primeRank 3 P = 2 at h3
  omega

/-- The unitary-five-four row contradicts the two original odd-rank markings. -/
theorem source_a5_oddNormalizer_component_not_unitary_five_four_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
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
  let W := ((D.fullModule.subgroupOf N).subgroupOf K).map (QuotientGroup.mk' (center K))
  obtain ⟨hP,hW,hE,_,hPW,h3,h5⟩ :=
    source_a5_oddNormalizer_component_quotient_local_marking_of_residual_le
      D e hn B hBC hodd hBV K hFK
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
  apply Theory.SpecificGroups.UnitaryFive.PerfectLocals.no_perfect_three_five_rank_two_in_twoLocal
    (HermitianForm.IdentityGram.identityGram J) hc hconj rfl f hf
    (by exact h3.ge) (by exact h5.ge) (M.map t.toMonoidHom)
    (Theory.GroupTheory.isTwoLocal_map t hM) hl
end CFSG.Quasithin.Chapter10
