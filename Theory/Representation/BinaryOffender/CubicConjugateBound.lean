module

public import Theory.Representation.BinaryOffender.CubicConjugateBound.CentralQuotient

public import Theory.Representation.BinaryOffender.ConjugateDisplacement
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.NormalInvariants
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Degree bounds for actual cubic actors

A cubic actor of ratio at most n contains an involution of displacement at
most n times the ambient two-rank. If k conjugates of each involution generate
a subgroup containing an irreducibly acting faithful component, the binary
degree is at most k times this displacement bound. All elements and fixed
spaces belong to the original representation, including outer involutions.

This is the binary form of Guralnick–Malle, *Classification of 2F-modules I*,
§2, inequalities (2.5)–(2.6), used in Aschbacher–Smith K.2, printed p.453.
-/

public section
namespace Representation.BinaryOffender
open Subgroup
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Binary rank of an elementary subgroup is bounded by ambient two-rank. -/
theorem rank_le_of_primeRank_le {A : Subgroup G} (hA : IsElementaryTwo A)
    {r : ℕ} (hr : primeRank 2 G ≤ r) : rank A ≤ r := by
  have hc := (primeRank_le_iff_elementary_card_le G).mp hr A hA.2
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

/-- Any nonidentity element of a cubic actor inherits its displacement bound. -/
theorem involution_fixedCodim_le_of_mem_small_actor
    (ρ : Representation (ZMod 2) G V) {A : Subgroup G}
    (hA : IsElementaryTwo A) {n r : ℕ} (hr : primeRank 2 G ≤ r)
    (hsmall : fixedCodim ρ A ≤ n * rank A) {t : G} (ht : t ∈ A) :
    t ^ 2 = 1 ∧ fixedCodim ρ (zpowers t) ≤ n * r := by
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨elemPow_eq_one_of_isElementaryAbelian t ht, ?_⟩
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hdim := Submodule.finrank_mono hle
  have hdimA := fixedCodim_add_finrank ρ A
  have hdimt := fixedCodim_add_finrank ρ (zpowers t)
  have hbound := Nat.mul_le_mul_left n (rank_le_of_primeRank_le hA hr)
  omega

/-- A small cubic ratio supplies an involution in the actual acting group. -/
theorem exists_small_involution_of_cubicRatio_le
    (ρ : Representation (ZMod 2) G V) {n r : ℕ}
    (hr : primeRank 2 G ≤ r) (hq : cubicRatio ρ ≤ (n : ℝ≥0∞)) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ fixedCodim ρ (zpowers t) ≤ n * r := by
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ n).mp hq
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  obtain ⟨ht2, hdim⟩ := involution_fixedCodim_le_of_mem_small_actor ρ hA hr hsmall ht
  exact ⟨t, ht1, ht2, hdim⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Faithful irreducibility on a nontrivial subgroup excludes fixed vectors. -/
theorem fixedSpace_eq_bot_of_faithful_irreducible_on
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [Nontrivial L]
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype)) :
    fixedSpace ρ L = ⊥ := by
  let σ : Representation (ZMod 2) L V := ρ.comp L.subtype
  let : σ.IsIrreducible := hi
  have hz : invariants (σ.comp (⊤ : Subgroup L).subtype) = ⊥ := by
    by_contra hn
    have hk := σ.le_ker_of_normal_invariants_ne_bot ⊤ hn
    obtain ⟨g, hg⟩ := exists_ne (1 : L)
    apply hg
    apply Subtype.val_injective
    apply hf
    exact (hk (mem_top g)).trans (map_one ρ).symm
  apply le_bot_iff.mp
  intro v hv
  have hv' : v ∈ invariants (σ.comp (⊤ : Subgroup L).subtype) := fun g => hv g.val
  simpa only [hz, Submodule.mem_bot] using hv'

/-- Conjugate generation turns the cubic-ratio bound into a binary degree bound. -/
theorem finrank_le_of_cubicRatio_conjugates
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [Nontrivial L]
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {n r k : ℕ} (hr : primeRank 2 G ≤ r)
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin k → G, L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹))
    (hq : cubicRatio ρ ≤ (n : ℝ≥0∞)) :
    Module.finrank (ZMod 2) V ≤ k * (n * r) := by
  obtain ⟨t, ht, ht2, hd⟩ := exists_small_involution_of_cubicRatio_le ρ hr hq
  obtain ⟨g, hg⟩ := hgen t ht ht2
  exact (finrank_le_mul_fixedCodim_of_conjugate_generation ρ L
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L hf hi) t g hg).trans
      (Nat.mul_le_mul_left k hd)

end Representation.BinaryOffender
