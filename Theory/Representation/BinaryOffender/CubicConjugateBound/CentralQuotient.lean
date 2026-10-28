module

public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.ConjugateDisplacement
public import Theory.Representation.BinaryIrreducibleRank
public import Theory.Representation.NormalInvariants
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.Representation.BinaryOffender.CubicConjugateDimension

/-!
# Degree bounds for cubic actors in the actual acting group

A cubic actor of ratio at most a supplies an involution of displacement at
most a times the ambient two-rank. If k conjugates of every involution generate
over an irreducibly and faithfully acting nontrivial subgroup, the binary degree
is at most k times that displacement. For a perfect normal subgroup its actual
central quotient bounds the ambient two-rank, including central covers.

These are the characteristic-two estimates (2.5)--(2.6) of Guralnick--Malle,
Classification of 2F-modules I, manuscript p.4, used in Aschbacher--Smith K.2,
printed p.453. The acting group and representation are retained throughout;
no full linear normalizer or absolute irreducibility assumption is introduced.
-/

public section
namespace Representation.BinaryOffender
open Subgroup Theory.GroupTheory
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An actual cubic actor supplies a small-displacement involution in G. -/
theorem exists_involution_of_cubicRatio_le_nat {a : ℕ}
    (hq : cubicRatio ρ ≤ (a : ℝ≥0∞)) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧
      fixedCodim ρ (zpowers t) ≤ a * primeRank 2 G := by
  obtain ⟨A, hA, _, hd⟩ := (cubicRatio_le_nat_iff ρ a).mp hq
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  refine ⟨t, ht1, elemPow_eq_one_of_isElementaryAbelian t ht, ?_⟩
  have hc := (primeRank_le_iff_elementary_card_le G).mp le_rfl A hA.2
  have hr : rank A ≤ primeRank 2 G := by
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv x
    exact hv ⟨x, (zpowers_le.mpr ht) x.property⟩
  have hfin := Submodule.finrank_mono hle
  have hdimA := fixedCodim_add_finrank ρ A
  have hdimt := fixedCodim_add_finrank ρ (zpowers t)
  exact (show fixedCodim ρ (zpowers t) ≤ fixedCodim ρ A by omega).trans
    (hd.trans (Nat.mul_le_mul_left a hr))

omit [FiniteDimensional (ZMod 2) V] in
/-- The central quotient bounds the rank of the actual ambient group. -/
theorem primeRank_le_central_quotient_automorphisms_of_irreducible
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    [IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    {S : Type*} [Group S] (e : L ⧸ center L ≃* S) :
    primeRank 2 G ≤ primeRank 2 (MulAut S) :=
  primeRank_le_central_quotient_automorphisms ρ L hf inferInstance e

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness and irreducibility on a nontrivial subgroup give zero fixed space. -/
theorem fixedSpace_eq_bot_of_faithful_irreducible_restriction
    (L : Subgroup G) [Nontrivial L] [IsIrreducible (ρ.comp L.subtype)]
    (hf : Function.Injective ρ) : fixedSpace ρ L = ⊥ := by
  let σ : Representation (ZMod 2) L V := ρ.comp L.subtype
  have he : fixedSpace σ ⊤ = fixedSpace ρ L := by
    ext v
    exact ⟨fun h l => h ⟨l, mem_top l⟩, fun h l => h l⟩
  by_contra h
  have hn : fixedSpace σ ⊤ ≠ ⊥ := by rwa [he]
  have hk := Representation.le_ker_of_normal_invariants_ne_bot σ ⊤ hn
  obtain ⟨l, hl⟩ := exists_ne (1 : L)
  apply hl
  apply L.subtype_injective
  apply hf
  exact (MonoidHom.mem_ker.mp (hk (mem_top l))).trans (map_one σ).symm

/-- The degree estimate uses conjugates in the same group as the cubic actor. -/
theorem finrank_le_of_cubicRatio_and_conjugates
    (L : Subgroup G) (hfix : fixedSpace ρ L = ⊥) {a k r : ℕ}
    (hr : primeRank 2 G ≤ r)
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin k → G, L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹))
    (hq : cubicRatio ρ ≤ (a : ℝ≥0∞)) :
    Module.finrank (ZMod 2) V ≤ k * (a * r) := by
  obtain ⟨t, ht, ht2, hd⟩ := exists_involution_of_cubicRatio_le_nat ρ hq
  obtain ⟨g, hg⟩ := hgen t ht ht2
  exact (finrank_le_mul_fixedCodim_of_conjugate_generation ρ L hfix t g hg).trans
    (Nat.mul_le_mul_left k (hd.trans (Nat.mul_le_mul_left a hr)))

/-- A genuine central-quotient model can supply the rank input to (2.6). -/
theorem finrank_le_of_cubicRatio_central_quotient
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L] [Nontrivial L]
    [IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    {S : Type*} [Group S] (e : L ⧸ center L ≃* S) {a k r : ℕ}
    (hr : primeRank 2 (MulAut S) ≤ r)
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin k → G, L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹))
    (hq : cubicRatio ρ ≤ (a : ℝ≥0∞)) :
    Module.finrank (ZMod 2) V ≤ k * (a * r) :=
  finrank_le_of_cubicRatio_and_conjugates ρ L
    (fixedSpace_eq_bot_of_faithful_irreducible_restriction ρ L hf)
    ((primeRank_le_central_quotient_automorphisms_of_irreducible ρ L hf e).trans hr) hgen hq

end Representation.BinaryOffender
