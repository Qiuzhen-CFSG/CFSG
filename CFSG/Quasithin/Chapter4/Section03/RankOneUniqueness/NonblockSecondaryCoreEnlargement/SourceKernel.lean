module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceConstruction
public import Theory.GroupTheory.CComponent.FullRankOuterAction
public import Theory.SpecificGroups.PSL3Four.ThreeRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The original linear-four action kernel has order prime to three

Use the actual normal component and the actual quotient of the root
normalizer by its two-core. The component image has trivial center and
cubic rank at least two; the original SQTK hypothesis bounds the ambient
cubic rank by two. Its centralizer is therefore prime to three, and the
full kernel-preimage calculation proves the same for the original action
on K_Z/O₂(K_Z).

The full PSL₃(4) marking is an explicit terminal-row input. This result
supplies the kernel-order premise needed to eliminate scalar compensation
on a fully marked adjoint Frattini module; it does not construct that module.
Source: Aschbacher–Smith A.3.18 and original 4.3.12–16, pp.51–53,617–618.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open CComponentPrimeRank
section KernelPreimage
variable {G : Type*} [Group G] [Finite G]

/-- The quotient-action kernel is the full preimage of the centralizer of
the actual component image modulo the ambient two-core. -/
private theorem quotientAction_ker_eq_centralizer_preimage (B : Subgroup G) [B.Normal]
    (hB : B.IsCComponent) :
    (normalQuotientAction B (pCore 2 B)).ker =
      (centralizer (B.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G))).comap
        (QuotientGroup.mk' (pCore 2 G)) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let I := B.map q
  let : I.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  rw [show centralizer (B.map q : Set (G ⧸ pCore 2 G)) =
    (MulAut.conjNormal : (G ⧸ pCore 2 G) →* MulAut I).ker from
      (MulAut.conjNormal_ker_eq_centralizer I).symm]
  ext x
  change normalQuotientAction B (pCore 2 B) x = 1 ↔
    (MulAut.conjNormal (q x) : MulAut I) = 1
  rw [←twoCoreQuotientAction_compatible B hB x]
  exact (MulAut.congr (cComponentTwoCoreQuotientEquiv hB)).map_eq_one_iff.symm

/-- At full odd prime rank, the literal intrinsic quotient action has
prime-to-p kernel, including its part in the ambient two-core. -/
private theorem quotientAction_ker_coprime (B : Subgroup G) [B.Normal]
    (hB : B.IsCComponent) {p : ℕ} [Fact p.Prime]
    (hz : Nat.Coprime p (Nat.card (center (B ⧸ pCore 2 B))))
    (hr : 2 ≤ primeRank p (B ⧸ pCore 2 B))
    (hG : primeRank p G ≤ 2) (ho : Odd p) :
    Nat.Coprime p (Nat.card (normalQuotientAction B (pCore 2 B)).ker) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let I := B.map q
  let e := cComponentTwoCoreQuotientEquiv hB
  let C := centralizer (I : Set (G ⧸ pCore 2 G))
  have hzI : Nat.Coprime p (Nat.card (center I)) := by
    rwa [←Nat.card_congr (centerCongr e).toEquiv]
  have hrI : 2 ≤ primeRank p I := by rwa [←primeRank_congr p e]
  have hQ : primeRank p (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans hG
  have hC : Nat.Coprime p (Nat.card C) :=
    Theory.GroupAction.ComponentRankAction.centralizer_coprime I hzI hrI hQ
  let A := (normalQuotientAction B (pCore 2 B)).ker
  let f := q.comp A.subtype
  have hfC : f.range ≤ C := by
    rintro _ ⟨x,rfl⟩
    exact (quotientAction_ker_eq_centralizer_preimage B hB).le x.property
  have hrange : Nat.Coprime p (Nat.card f.range) := hC.of_dvd_right (card_dvd_of_le hfC)
  have hker : Nat.Coprime p (Nat.card f.ker) := by
    have hq : Nat.Coprime p (Nat.card q.ker) := by
      rw [QuotientGroup.ker_mk']
      obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p:=2) (G:=G))
      rw [hk]
      exact (Nat.coprime_two_right.mpr ho).pow_right k
    exact hq.of_dvd_right (card_comap_dvd_of_injective q.ker A.subtype A.subtype_injective)
  have hc := f.ker.index_mul_card
  rw [index_ker] at hc
  exact hc ▸ hrange.mul_right hker


end KernelPreimage
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The literal source action, with no strict-enlargement premise, has cubic-prime kernel. -/
theorem SecondaryActionData.action_kernel_coprime_three (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL) :
    Nat.Coprime 3 (Nat.card s.action.ker) := by
  let := s.normal
  let : Group.IsPerfect Matrix.PSL3Four.SL := Atlas.sl_perfect 3 (by decide)
  have hz : Nat.Coprime 3 (Nat.card (center (s.component ⧸ pCore 2 s.component))) := by
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Group.IsPerfect.center_quotient_center_eq_bot Matrix.PSL3Four.SL]
    simp
  apply quotientAction_ker_coprime s.component s.isComponent hz
  · rw [primeRank_congr 3 e]
    exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two
  · exact (EndgameSieve.rootNormalizer_sqtk c D h).stronglyQuasithin 3 Nat.prime_three (by decide)
  · decide

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
