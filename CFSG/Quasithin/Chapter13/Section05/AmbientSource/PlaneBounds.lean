module
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Plane
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner

/-!
# Core containment and the odd rank of the plane centralizer

The actual normal closure from 13.3.15 has symmetric-three quotient by
its two-core. Relative normality puts this core in the plane normalizer's
core, giving the required containment of C_Q₁(V₂). The plane centralizer
commutes with the normal closure modulo that core. The centreless S₃
quotient contributes an independent cubic rank, so its centralizer has
three-rank at most one when the plane normalizer has three-rank at most two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.3.15(4–5), printed pp.893–894; reused in 13.5.4(3), printed p.916.
The preceding noncentrality and actual cubic parabolic inputs remain
explicit, exactly as in the normal-closure producer.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsKleinFour
namespace CFSG.Quasithin.Chapter13.Section05.AmbientSource
variable {G : Type*} [Group G] [Finite G]

/-- The centralizing part of the original point-core lies in both literal plane cores. -/
theorem point_core_centralizer_le_plane_cores (T : Sylow 2 G) (P E X : Subgroup G) [IsKleinFour E]
    (hP : Nat.card P = 2) (hPE : P ≤ E)
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (hTE : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G))
    (hm : ⁅(normalizer (P : Set G)).pCoreIn 2, E⁆ ≠ ⊥) :
    (normalizer (P : Set G)).pCoreIn 2 ⊓ centralizer (E : Set G) ≤
      (X ⊔ (normalizer (P : Set G)).pCoreIn 2).pCoreIn 2 ∧
    (X ⊔ (normalizer (P : Set G)).pCoreIn 2).pCoreIn 2 ≤
      (normalizer (E : Set G)).pCoreIn 2 := by
  obtain ⟨hspan, _, hcore, _⟩ := plane_normalClosure T P E X hP hPE hTP hTE hXN hTX hX hx hkX hm
  constructor
  · rw [hcore]
    exact inf_le_inf le_sup_right le_rfl
  · apply pCoreIn_mono_of_normalizes
    · exact sup_le hXN (point_core_le_plane_normalizer T P E hTP hTE)
    · rw [← hspan]
      exact le_normalizer_conjugateSpanBy _ _

private theorem symmetricThree_rank_pos : 1 ≤ primeRank 3 (Equiv.Perm (Fin 3)) := by
  let A := alternatingGroup (Fin 3)
  have hc : Nat.card A = 3 := by
    change Nat.card (alternatingGroup (Fin 3)) = 3
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let : IsCyclic A := isCyclic_of_prime_card hc
  let : CommGroup A := IsCyclic.commGroup
  exact primeRank_ge_of_elementary_embedding
    (fun a : A => by simpa only [hc] using pow_card_eq_one' (x := a))
    (by simpa only [pow_one] using hc) A.subtype A.subtype_injective
/-- The original plane centralizer has three-rank at most one. -/
theorem plane_centralizer_three_rank (T : Sylow 2 G) (P E X : Subgroup G) [IsKleinFour E]
    (hP : Nat.card P = 2) (hPE : P ≤ E)
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (hTE : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G))
    (hm : ⁅(normalizer (P : Set G)).pCoreIn 2, E⁆ ≠ ⊥)
    (hr : primeRank 3 (normalizer (E : Set G)) ≤ 2) :
    primeRank 3 (centralizer (E : Set G)) ≤ 1 := by
  obtain ⟨hspan, _, hcore, ⟨e⟩⟩ := plane_normalClosure T P E X hP hPE hTP hTE hXN hTX hX hx hkX hm
  let I := X ⊔ (normalizer (P : Set G)).pCoreIn 2
  let C := centralizer (E : Set G)
  have hIN : I ≤ normalizer (E : Set G) :=
    sup_le hXN (point_core_le_plane_normalizer T P E hTP hTE)
  have hn : normalizer (E : Set G) ≤ normalizer (I : Set G) := by
    dsimp only [I]
    rw [← hspan]
    exact le_normalizer_conjugateSpanBy _ _
  have hCnorm : I ≤ normalizer (C : Set G) := hIN.trans ((normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (E : Set G))).mp inferInstance)
  have hc : ⁅(pResidual 2 C).map C.subtype,I⁆ ≤ I.pCoreIn 2 := by
    rw [hcore]
    apply le_inf
    · exact (commutator_mono (map_subtype_le _) le_rfl).trans
        (le_normalizer_iff_commutator_le_right.mp ((Subgroup.centralizer_le_normalizer (E : Set G)).trans hn))
    · exact (commutator_mono (map_subtype_le _) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hCnorm)
  have hz : Nat.Coprime 3 (Nat.card (center (I ⧸ pCore 2 I))) := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    have he : center (Equiv.Perm (Fin 3)) = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      exact Theory.GroupTheory.NormalSymmetricThreePairRank.symmetricThree_center_trivial a
        (mem_center_iff.mp ha)
    rw [he, Nat.card_unique]
    decide
  have hsum := Theory.GroupTheory.ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) C I ((Subgroup.centralizer_le_normalizer (E : Set G)).trans hn) hc hz
  have hlow : 1 ≤ primeRank 3 I := by
    have he := primeRank_congr 3 e
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup] at he
    exact he.symm ▸ symmetricThree_rank_pos
  have hup := (primeRank_mono 3 (sup_le (Subgroup.centralizer_le_normalizer (E : Set G)) hIN)).trans hr
  change primeRank 3 (C ⊔ I : Subgroup G) ≤ 2 at hup
  change primeRank 3 C ≤ 1
  omega

end CFSG.Quasithin.Chapter13.Section05.AmbientSource
