module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.LocalCriteria
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Constructing Sylow three from a torus normalizer

Let A be a subgroup whose index is not divisible by nine. Its Sylow-three
subgroup T has the same property. An element of order three outside T that
normalizes T therefore generates, together with T, a Sylow subgroup of the
ambient group. This argument imposes no bound on the three-part of |A|.

The configuration below records elements and equations in the base group,
including the alternating-pairing detector on T. The constructed Sylow
subgroup feeds the existing perfect-central-cover transfer theorem. The
split and nonsplit triality torus constructions must supply the configuration;
its existence is not asserted here.

Source: the nondefining-characteristic calculation underlying GLS3 §6.1,
Theorem 6.1.4 and Tables 6.1.2–3; central transfer in Aschbacher–Smith I.1.1–2.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal

open Subgroup PerfectCentralCovering PerfectCentralCovering.OddSylow

variable {G : Type*} [Group G] [Finite G]

/-- The primary part of a subgroup retains the condition on its ambient index. -/
theorem nine_not_dvd_primary_index (A : Subgroup G) (P : Sylow 3 A)
    (hi : ¬ 9 ∣ A.index) : ¬ 9 ∣ ((P : Subgroup A).map A.subtype).index := by
  rw [index_map_of_injective _ A.subtype_injective, range_subtype]
  have hc : Nat.Coprime 9 (P : Subgroup A).index :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).pow_left 2
  exact fun h => hi (hc.dvd_mul_left.mp h)

/-- A normalized cyclic supplement accounts for the final factor of three
in the group order. Normalization is relative to T, not to the ambient group. -/
theorem exists_sylow_of_normalizer (T : Subgroup G)
    (hT : IsPGroup 3 T) (hi : ¬ 9 ∣ T.index) (c : G)
    (hc : orderOf c = 3) (hout : c ∉ T)
    (hn : c ∈ normalizer (T : Set G)) :
    ∃ Q : Sylow 3 G, (Q : Subgroup G) = T ⊔ zpowers c := by
  have hcn : zpowers c ≤ normalizer (T : Set G) := zpowers_le.mpr hn
  have hdis := T.disjoint_zpowers_of_prime_order_not_mem c hc hout
  let H := T ⊔ zpowers c
  have hcard : Nat.card H = Nat.card T * 3 := by
    dsimp [H]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint T _ hcn hdis, Nat.card_zpowers, hc]
  have hindex : 3 * H.index = T.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T))
    rw [← mul_assoc, ← hcard, H.card_mul_index, T.card_mul_index]
  have hHindex : ¬ 3 ∣ H.index := by
    intro h
    apply hi
    rw [← hindex]
    exact Nat.mul_dvd_mul_left 3 h
  have hcp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hc, pow_one])
  exact ⟨(hT.to_sup_of_normal_left' hcp hcn).toSylow hHindex, rfl⟩

/-- Concrete torus data, before proving that the generated subgroup is Sylow.
The pair generators may have different orders. In particular this does not
impose the equal-factor torus of the G₂ calculation on triality. -/
structure Configuration (A : Subgroup G) where
  primary : Sylow 3 A
  pair : TorusPair ((primary : Subgroup A).map A.subtype)
  cycle : G
  inverter : G
  cycle_order : orderOf cycle = 3
  cycle_outside : cycle ∉ (primary : Subgroup A).map A.subtype
  normalizes : cycle ∈ normalizer (((primary : Subgroup A).map A.subtype : Subgroup G) : Set G)
  inverts : ∀ t ∈ (primary : Subgroup A).map A.subtype,
    inverter * t * inverter⁻¹ = t⁻¹
  fixes : Commute inverter cycle

/-- The actual primary torus and cyclic supplement construct the geometry
required by central transfer; the ambient Sylow witness is an output. -/
theorem Configuration.geometry {A : Subgroup G} (d : Configuration A)
    (hi : ¬ 9 ∣ A.index) : Geometry 3 G := by
  obtain ⟨Q, hQ⟩ := exists_sylow_of_normalizer _
    (d.primary.isPGroup'.map A.subtype) (nine_not_dvd_primary_index A d.primary hi)
    d.cycle d.cycle_order d.cycle_outside d.normalizes
  exact Geometry.normalizer Q _ d.pair d.cycle d.inverter hQ.symm
    d.normalizes d.inverts d.fixes

/-- Application to arbitrary finite perfect central covers, in any universe. -/
theorem Configuration.not_three_dvd_kernel {A : Subgroup G} (d : Configuration A)
    (hi : ¬ 9 ∣ A.index) {E : Type*} [Group E] [Finite E] (f : Cover E G) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker :=
  (d.geometry hi).not_dvd_card_kernel (by decide) f

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal
