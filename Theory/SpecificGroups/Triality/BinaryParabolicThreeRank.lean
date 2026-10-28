module

public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear

/-!
# Three-rank of the full binary triality parabolics

For the genuine descended parabolics of ³D₄(2), the three-rank is at most one.
Their local factors have two-group kernels and actual PSL₂(q³) and PSL₂(q)
quotients. Odd p-subgroups of characteristic-two SL₂ are cyclic, so these
quotients have three-rank at most one; the two-group kernels contribute zero.

To pass to the full parabolics, retain the quotient by the embedded O^{2′}.
The original descended torus supplements that normal subgroup and has order
(q³ - 1)(q - 1). At q = 2 this is seven, so the full-parabolic quotient has
order dividing seven and also contributes zero to three-rank. All normality
and quotient calculations take place inside the parabolic. No perfectness
assertion is needed at the binary parameter.

Sources: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528,
and F.1.11–12, printed pp.262–264 (`refs/quasithin.pdf`); GLS3 §§2.4 and 2.6
(`refs/KGroup/GLS3/chapter2.tex`). The Geck root, elementary fixed-point and
central-quotient constructions are those of the imported local structure.
-/

public section

open scoped MatrixGroups
open Theory.GroupTheory

namespace Triality.Standard.Parabolics
noncomputable section

private theorem prime_eq_two (P : Parameters) (hq : P.q = 2) : P.prime = 2 := by
  apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
  rw [← hq]
  exact dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)

private theorem three_rank_psl2 (F : Type*) [Field F] [Finite F] [CharP F 2] :
    primeRank 3 PSL(2, F) ≤ 1 := by
  let S : Sylow 3 SL(2, F) := default
  apply S.primeRank_le_one_of_surjective
    (Matrix.SL2.odd_pGroup_isCyclic_of_injective S.isPGroup' (by decide)
      (S : Subgroup SL(2, F)).subtype (S : Subgroup SL(2, F)).subtype_injective)
    (Theory.PSL2.sl2QuotientEquiv F).toMonoidHom
    (Theory.PSL2.sl2QuotientEquiv F).surjective

/-- The root Levi quotients bound the three-rank of both local factors in characteristic two. -/
theorem localFactor_threeRank_le_one (P : Parameters) (hp : P.prime = 2) (a : Node) :
    primeRank 3 (localFactor P a) ≤ 1 := by
  have hcore : primeRank 3 (pCore 2 (localFactor P a)) = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := localFactor P a)).exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hquot : primeRank 3 (localFactor P a ⧸ pCore 2 (localFactor P a)) ≤ 1 := by
    cases a with
    | arms =>
      let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
      rw [primeRank_equiv 3 (localFactorArmsQuotientEquivPSL2 P hp)]
      exact three_rank_psl2 _
    | central =>
      let : CharP (GaloisField P.prime P.exponent) 2 :=
        hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
      rw [primeRank_equiv 3 (localFactorCentralQuotientEquivPSL2 P hp)]
      exact three_rank_psl2 _
  have h := primeRank_le_ker_add (p := 3) (QuotientGroup.mk' (pCore 2 (localFactor P a)))
  rw [QuotientGroup.ker_mk', hcore, zero_add] at h
  exact h.trans hquot

/-- The quotient of either full binary parabolic by its local factor has order dividing seven. -/
theorem localFactor_relIndex_dvd_seven (P : Parameters) (hq : P.q = 2) (a : Node) :
    (localFactor P a).relIndex (parabolic P a) ∣ 7 := by
  have hp := prime_eq_two P hq
  let N := (localFactor P a).subgroupOf (parabolic P a)
  let T := (ConcreteBruhat.torus P).subgroupOf (parabolic P a)
  have ht := (ConcreteBruhat.torus_le_borel P).trans (borel_le_parabolic P a)
  have htop : N ⊔ T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (localFactor_le_parabolic P a) ht,
      ← parabolic_eq_localFactor_sup_torus P hp a, Subgroup.subgroupOf_self]
  have hi : N.index = N.relIndex T := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_left]
  have hc : Nat.card T = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ht).toEquiv,
      ConcreteBruhat.TorusCoordinates.card_torus P hp, hq]
    norm_num
  change N.index ∣ 7
  rw [hi, ← hc]
  exact Subgroup.relIndex_dvd_card _ _

/-- Both full genuine parabolics of ³D₄(2) have three-rank at most one. -/
theorem parabolic_threeRank_le_one_of_q_eq_two
    (P : Parameters) (hq : P.q = 2) (a : Node) :
    primeRank 3 (parabolic P a) ≤ 1 := by
  let N := (localFactor P a).subgroupOf (parabolic P a)
  have hquot : primeRank 3 (parabolic P a ⧸ N) = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    intro hd
    have hi : Nat.card (parabolic P a ⧸ N) ∣ 7 :=
      localFactor_relIndex_dvd_seven P hq a
    exact (by decide : ¬ 3 ∣ 7) (hd.trans hi)
  have hN : primeRank 3 N ≤ 1 := by
    rw [primeRank_equiv 3 (Subgroup.subgroupOfEquivOfLe (localFactor_le_parabolic P a))]
    exact localFactor_threeRank_le_one P (prime_eq_two P hq) a
  have h := primeRank_le_ker_add (p := 3) (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', hquot, add_zero] at h
  exact h.trans hN

end
end Triality.Standard.Parabolics
