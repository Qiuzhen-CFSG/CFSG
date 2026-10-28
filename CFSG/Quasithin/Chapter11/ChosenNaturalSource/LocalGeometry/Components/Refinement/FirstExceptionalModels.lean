module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.SpecificGroups.Triality.StandardTwoRank.Automorphisms
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus
public import Theory.SpecificGroups.Triality.BinarySevenPlane
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
/-!
# Model actors for the first-normalizer exceptional rows

A primitive divisor of 2^n−1 has order n modulo that prime and is therefore
larger than n. It misses the field-automorphism order of G₂, and, in the odd
degrees used by the consumer, the full triality outer order 3n. The literal
tori give rank two at this prime. For the cube-field endpoint ³D₄(2), the
proved concrete seven-plane gives the corresponding rank-two witness.

These model lemmas feed `FirstExceptionalLie`, which passes the actual
relative component through the ambient two-core and contradicts its
intersection with the faithful Cartan factor. They assert no embedding
classification. The model constructions and their attribution are retained
in the imported modules; no new finite matrix certificate is introduced.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.761--762, and A.3.18, printed pp.51--53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.ExceptionalActors
theorem primitive_split_prime {n : ℕ} (hn : 1 < n) (hn6 : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ Odd p ∧ p ∣ 2 ^ n - 1 := by
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two hn hn6
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    change orderOf (0 : ZMod 2) = n at ho
    rw [orderOf_zero] at ho
    omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp he) |>.resolve_left hp.ne_one)
  have hd := ZMod.orderOf_dvd_card_sub_one htwo
  rw [ho] at hd
  have hnp : n < p := by
    have := Nat.le_of_dvd (show 0 < p - 1 by have := hp.two_le; omega) hd
    omega
  refine ⟨p,hp,hnp,hp.odd_of_ne_two hp2,?_⟩
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  rw [Nat.cast_sub Nat.one_le_two_pow,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  exact sub_eq_zero.mpr (ho ▸ pow_orderOf_eq_one (2 : ZMod p))

theorem g2_split_rank {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F - 1) :
    2 ≤ primeRank p (Atlas.G2.Model F) := by
  have hu : 1 ≤ primeRank p Fˣ := by
    by_contra hh
    have hz : primeRank p Fˣ = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by simpa only [Nat.card_units] using hd)
  have hi := primeRank_le_of_injective p (Atlas.G2.torusHom (K := F)) Atlas.G2.torusHom_injective
  rw [primeRank_prod_eq_add] at hi
  omega

theorem g2_primePower_inner {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hF : Nat.card F = 2 ^ n) (hq : 2 < Nat.card F)
    (hp : p.Prime) (hnp : n < p) (a : MulAut (Atlas.G2.Model F))
    (m : ℕ) (ha : a ^ (p ^ m) = 1) :
    a ∈ MulAut.innerSubgroup (Atlas.G2.Model F) := by
  let φ := Atlas.G2.LieAutomorphismExtensions.fieldComponent (F := F) hq
  have hcard : Nat.card (F ≃+* F) = n := FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF
  have hn : 0 < n := by
    by_contra hh
    have hn : n = 0 := by omega
    rw [hn,pow_zero] at hF
    omega
  have hc : Nat.Coprime (p ^ m) (Nat.card (F ≃+* F)) := by
    rw [hcard]
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      hn hnp)).pow_left m
  have hpow : (φ a) ^ (p ^ m) = 1 := by rw [← map_pow,ha,map_one]
  have he : φ a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_natCard _))
  obtain ⟨g,hg⟩ := (Atlas.G2.LieAutomorphismExtensions.fieldComponent_eq_one_iff hq a).mp he
  exact ⟨g,hg.symm⟩

theorem outer_primePower_inner {A : Type*} [Group A] [Finite A]
    {d p : ℕ} (hd : Nat.card (MulAut.Outer A) ∣ d) (hc : Nat.Coprime p d)
    (a : MulAut A) (k : ℕ) (ha : a ^ (p ^ k) = 1) :
    a ∈ MulAut.innerSubgroup A := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup A)
  apply (QuotientGroup.eq_one_iff _).mp
  change q a = 1
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes ((hc.pow_left k).coprime_dvd_right hd)
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ha, map_one]
  · exact orderOf_dvd_natCard _

private theorem units_prime_rank {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F - 1) :
    1 ≤ primeRank p Fˣ := by
  by_contra hh
  have hz : primeRank p Fˣ = 0 := by omega
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by simpa only [Nat.card_units] using hd)

theorem triality_split_rank {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hd : p ∣ 2 ^ n - 1) :
    2 ≤ primeRank p (Triality.Standard.BinaryCarrier n hn) := by
  let P := Triality.Standard.binaryParameters n hn
  have hu : 1 ≤ primeRank p (Triality.Standard.ExtensionField P)ˣ := by
    apply units_prime_rank
    rw [Triality.Standard.card_extensionField]
    change p ∣ (2 ^ n) ^ 3 - 1
    exact hd.trans (Nat.sub_one_dvd_pow_sub_one _ _)
  have hv : 1 ≤ primeRank p (Triality.Standard.fixedField P)ˣ := by
    apply units_prime_rank
    rw [Triality.Standard.card_fixedField]
    exact hd
  let e := Triality.Standard.ConcreteBruhat.TorusCoordinates.torusMulEquiv P rfl
  have hi := primeRank_le_of_injective p (Triality.Standard.ConcreteBruhat.torus P).subtype
    (Triality.Standard.ConcreteBruhat.torus P).subtype_injective
  rw [← primeRank_equiv p e] at hi
  change primeRank p ((Triality.Standard.ExtensionField P)ˣ ×
    (Triality.Standard.fixedField P)ˣ) ≤ _ at hi
  rw [primeRank_prod_eq_add] at hi
  change 2 ≤ primeRank p (Triality.Standard.Carrier P)
  omega

theorem triality_seven_rank :
    2 ≤ primeRank 7 (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative QuaternionSevenPlane.Plane)
    (fun a => ?_) (by simp [QuaternionSevenPlane.Plane, Nat.card_eq_fintype_card])
    Triality.Standard.binarySevenPlane.embedding Triality.Standard.binarySevenPlane.embedding_injective
  change (7 : ℕ) • a.toAdd = 0
  exact ZModModule.char_nsmul_eq_zero 7 a.toAdd


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.ExceptionalActors
