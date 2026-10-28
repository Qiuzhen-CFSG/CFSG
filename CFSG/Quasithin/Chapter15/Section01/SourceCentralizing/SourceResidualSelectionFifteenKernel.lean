module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison.Full
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.CoprimeRank

/-!
# The cubic rank of the third local's plane centralizer

The actual symmetric-three action and original intersection-core estimates
split N/O₂(N) as S₃ times C_N(V(N))/O₂(N). Quasithinness bounds the cubic
rank of N by two, while the symmetric-three factor contributes one.
Odd prime rank is unchanged by the two-core quotients, so the actual
centralizer C_N(V(N)) has cubic rank at most one.

This calculation applies to any maximal two-local N distinct from the
distinguished partner. It assumes neither ordering maximality of N nor
triviality of its action kernel modulo O₂(N). In particular it applies to
the original third local in the full marked-five row once its actual
symmetric-three action has been established.

Source: Aschbacher--Smith 14.1.17--18 and 15.2.5,
printed pp.979--981 and 1107--1108.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

private theorem symmetric_three_rank_pos : 1 ≤ primeRank 3 (Equiv.Perm (Fin 3)) := by
  let A := alternatingGroup (Fin 3)
  have hc : Nat.card A = 3 := by
    change Nat.card (alternatingGroup (Fin 3)) = 3
    rw [nat_card_alternatingGroup]
    norm_num
  let : IsCyclic A := isCyclic_of_prime_card hc
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (fun a : A => by simpa only [hc] using (pow_card_eq_one' (x := a)))
    (by simpa using hc) A.subtype A.subtype_injective

private theorem centralizer_rank_of_split
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {N : Subgroup G}
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (e : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3) ×
      ((centralizer (localModule T N : Set G)).subgroupOf N ⧸
        (pCore 2 N).subgroupOf ((centralizer (localModule T N : Set G)).subgroupOf N))) :
    primeRank 3 (N ⊓ centralizer (localModule T N : Set G) : Subgroup G) ≤ 1 := by
  let C := (centralizer (localModule T N : Set G)).subgroupOf N
  have hr := (hG.twoLocal_sqtk hN.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  have he := Theory.GroupTheory.primeRank_equiv 3 e
  rw [primeRank_prod_eq_add,
    primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 N) pCore_isPGroup,
    primeRank_quotient_eq_of_isTwoGroup 3 (by decide) ((pCore 2 N).subgroupOf C)
      pCore_isPGroup.comap_subtype] at he
  have hpos := symmetric_three_rank_pos
  have hC : C.map N.subtype = N ⊓ centralizer (localModule T N : Set G) := by
    rw [subgroupOf_map_subtype,inf_comm]
  have heC := Theory.GroupTheory.primeRank_equiv 3
    ((C.equivMapOfInjective N.subtype N.subtype_injective).trans (MulEquiv.subgroupCongr hC))
  omega

/-- The actual S₃ local action gives cubic rank at most one for its
centralizer, without requiring this local to be ordering-maximal. -/
theorem source_local_symmetricThree_centralizer_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {N Mc : Subgroup G}
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : N ≠ Mc)
    (e : internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3)) :
    primeRank 3 (N ⊓ centralizer (localModule T N : Set G) : Subgroup G) ≤ 1 := by
  let V := localModule T N
  let C := (centralizer (V : Set G)).subgroupOf N
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    ((le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _))
  let a := actionHom N V (le_normalizer_conjugateSpanBy _ _)
  let eq : (N ⧸ C) ≃* Equiv.Perm (Fin 3) :=
    ((QuotientGroup.quotientMulEquivOfEq (actionHom_ker N V
      (le_normalizer_conjugateSpanBy _ _)).symm).trans
      (QuotientGroup.quotientKerEquivRange a)).trans e
  obtain ⟨hmeet,hnoncentral,hcomm⟩ :=
    local_partner_core_inputs hG T hempty hN hu hmany hne
  obtain ⟨_,_,_,_,_,_,_,_,_,⟨eprod⟩,_⟩ :=
    sourceResidual_splitting N Mc V eq hmeet hnoncentral hcomm
  exact centralizer_rank_of_split hG T hN eprod

end CFSG.Quasithin.Chapter15.Section02
