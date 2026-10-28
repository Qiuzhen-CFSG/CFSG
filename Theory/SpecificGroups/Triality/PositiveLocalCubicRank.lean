module
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.Quasithin.PositiveLocalRank
public import Theory.Quasithin.Rank

/-!
# A local cubic witness in genuine binary triality

The central root Levi is the actual PSL₂ over the base field and contains
an element of order three. It normalizes the nontrivial root two-radical,
whose checked order is q¹¹. Thus its three-rank contributes to the
normalizer of that radical and hence to the two-local three-rank of the
original triality carrier. This includes q = 2 and the actual quotient by
the elementary fixed group's own center.

Source: Aschbacher–Smith A.3.8 and F.1.12(I)(4), printed pp.45–46 and 263;
GLS3 §§2.4–2.6 provide the marked radical and root-Levi constructions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard.PositiveLocalCubicRank
open Parabolics RadicalCoordinates

/-- The central root Levi normalizes a nontrivial two-radical and contains a cubic. -/
theorem carrier (P : Parameters) (hp : P.prime=2) :
    1 ≤ twoLocalPrimeRank 3 (Carrier P) := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  have hd : 3 ∣ Nat.card PSL(2,GaloisField P.prime P.exponent) :=
    (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F:=GaloisField P.prime P.exponent) (i:=(0:Fin 2)) (j:=(1:Fin 2)) (by decide)).trans
      (card_subgroup_dvd_card _)
  have hl : 1 ≤ primeRank 3 (levi P .central) := by
    rw [primeRank_equiv 3 (leviCentralEquivPSL2 P hp)]
    exact Theory.Quasithin.one_le_primeRank_of_dvd_card hd
  have hne : radical P .central ≠ ⊥ := by
    intro he
    have hc := radical_central_card P hp
    rw [he,card_bot] at hc
    have hbig : 1 < P.q^11 := one_lt_pow₀ (by have := P.q_ge_two; omega) (by decide)
    omega
  have hn : levi P .central ≤ normalizer (radical P .central : Set (Carrier P)) :=
    (levi_le_parabolic P .central).trans
      ((normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .central)).mp
        (radical_normal P .central))
  have hlocal : IsTwoLocal (normalizer (radical P .central : Set (Carrier P))) :=
    ⟨radical P .central,hne,radical_isPGroup P hp .central,rfl⟩
  exact (hl.trans (primeRank_mono 3 hn)).trans (hlocal.primeRank_le 3)

/-- The binary catalogue's literal triality carrier has positive local cubic rank. -/
theorem binary (f : ℕ) (hf : 0<f) :
    1 ≤ twoLocalPrimeRank 3 (Carrier (binaryParameters f hf)) :=
  carrier _ rfl
end Triality.Standard.PositiveLocalCubicRank
