module
public import CFSG.Quasithin.Chapter10.SourceA5OvergroupReduction
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The original tensor overgroup has the prescribed Sylow subgroup

Let T₁=N_T(L). An outside overgroup H containing L and T₁ with nontrivial
two-core has T₁ as a Sylow subgroup. A proper two-overgroup of T₁ would
already be an ambient Sylow because T₁ has index two in T. The existing
normalizer bound places it in M. It cannot normalize L, because N_M(L)
has index two, so H contains both original factors and hence L₀. Source
uniqueness above L₀ and that Sylow then forces H into M, a contradiction.

Only the nontrivial two-core input of source 9.3.3 remains explicit. The
proof does not assume L₀≤H, maximality of H, or Thompson centralization.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 9.3.4,
printed p.733, using source 1.2.7 and the original index-two stabilizer.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D
private theorem maximal_normalizer_index
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L.subgroupOf D.maximalLocal : Set D.maximalLocal)).index = 2 := by
  let M := D.maximalLocal
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_, hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ (L.subgroupOf M).Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  exact ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot).1

/-- Source 9.3.4 with its earlier nontrivial-core input retained literally. -/
theorem source_a5_local_outside_overgroup_sylow
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hcore : pCore 2 H ≠ ⊥)
    (hLH : L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hout : ¬ H ≤ D.maximalLocal) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hRT : R ≤ (T : Subgroup G) := inf_le_left
  have hi : R.relIndex (T : Subgroup G) = 2 := by
    have he : R.subgroupOf (T : Subgroup G) =
        (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    change (R.subgroupOf (T : Subgroup G)).index = 2
    rw [he]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  apply Chapter1.isSylowIn_iff.mpr
  refine ⟨T.isPGroup'.to_le hRT, hRH, ?_⟩
  intro U hU hRU hUH
  by_contra hneU
  obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
  have hRQ : R ≤ (Q : Subgroup G) := hRU.trans hUQ
  have hindexQ : R.relIndex (Q : Subgroup G) = 2 := by
    have hcardQ := relIndex_mul_relIndex (⊥ : Subgroup G) R (Q : Subgroup G) bot_le hRQ
    have hcardT := relIndex_mul_relIndex (⊥ : Subgroup G) R (T : Subgroup G) bot_le hRT
    simp only [relIndex_bot_left] at hcardQ hcardT
    rw [hi] at hcardT
    have hQT : Nat.card Q = Nat.card T := Nat.card_congr (Q.equiv T).toEquiv
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := R))
      (hcardQ.trans (hQT.trans hcardT.symm))
  have hiU : R.relIndex U = 2 := by
    have hd : R.relIndex U ∣ 2 := hindexQ ▸
      dvd_of_mul_right_eq _ (relIndex_mul_relIndex R U (Q : Subgroup G) hRU hUQ)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (hneU (le_antisymm (relIndex_eq_one.mp h) hRU)).elim
    · exact h
  have hUQeq : U = (Q : Subgroup G) := by
    have hh := relIndex_mul_relIndex R U (Q : Subgroup G) hRU hUQ
    rw [hiU, hindexQ] at hh
    exact le_antisymm hUQ (relIndex_eq_one.mp (by omega : U.relIndex (Q : Subgroup G) = 1))
  have hnormal : (R.subgroupOf U).Normal := normal_of_index_eq_two hiU
  have hUM : U ≤ D.maximalLocal :=
    ((normal_subgroupOf_iff_le_normalizer hRU).mp hnormal).trans
      (source_a5_sylow_stabilizer_normalizer_le D e hn)
  have hQM : (Q : Subgroup G) ≤ D.maximalLocal := hUQeq ▸ hUM
  have hUN : ¬ U ≤ normalizer (L : Set G) := by
    intro hUN
    have hLM : L ≤ D.maximalLocal :=
      (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
    have hQN : ((Q.subtype hQM : Sylow 2 D.maximalLocal) : Subgroup D.maximalLocal) ≤
        normalizer (L.subgroupOf D.maximalLocal : Set D.maximalLocal) := by
      rw [← subgroupOf_normalizer_eq hLM]
      intro x hx
      exact hUN (hUQeq.symm ▸ hx)
    apply (Q.subtype hQM).not_dvd_index
    have hd := index_dvd_of_le hQN
    rwa [maximal_normalizer_index D hn] at hd
  obtain ⟨x, hxU, hxN⟩ := SetLike.not_le_iff_exists.mp hUN
  obtain ⟨t, ht, htn, hpair, _⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hxconj : L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj t).toMonoidHom :=
    (source_nonnormal_maximal_pair D hn ht htn x (hUM hxU)).resolve_left
      (fun he => hxN (mem_normalizer_iff_map_conj_eq.mpr he))
  have hLtH : L.map (MulAut.conj t).toMonoidHom ≤ H := by
    rw [← hxconj]
    rintro _ ⟨l, hl, rfl⟩
    exact H.mul_mem (H.mul_mem (hUH hxU) (hLH hl)) (H.inv_mem (hUH hxU))
  have hOrbitH : localOrbit T L ≤ H := by
    rw [hpair]
    exact sup_le hLH hLtH
  obtain ⟨N, hN, hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
  have hNM := source_overgroup_eq_of_maximal_sylow D Q hQM hN
    (hOrbitH.trans hHN) ((hUQeq ▸ hUH).trans hHN)
  exact hout (hNM ▸ hHN)

end CFSG.Quasithin.Chapter10
