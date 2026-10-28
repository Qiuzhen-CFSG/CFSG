module
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation

/-!
# Fixed indices for coprime quintic actions

Fixed indices multiply across an invariant normal subgroup of a finite
nilpotent group. The conjugation form below uses literal relative quotients
and identifies fixed points with ambient centralizers. In particular, an
invariant quotient centralized by the actor contributes index one.

A five-group acting on a two-group of order at most 64 has fixed index at
most 16: the index is a power of two congruent to one modulo five. The same
orbit argument bounds a quintic action on a binary module of order 64,
and the product formula handles repeated summands.

These facts supply the numerical four-factor estimate in Aschbacher--Smith,
original 4.3.2, printed p.618, without assuming a chief-factor filtration.
-/

@[expose] public section
noncomputable section
open Subgroup
open Representation.BinaryFixedPoints

namespace Representation.BinaryFixedPoints
variable {A V W : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem invariant_card (ρ : Representation (ZMod 2) A V) [Finite V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 64) :
    4 ≤ Nat.card ρ.invariants := by
  let := action ρ
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hm := hp.card_modEq_card_fixedPoints (Multiplicative V)
  change Nat.card V % 5 = Nat.card (FixedPoints.subgroup A (Multiplicative V)) % 5 at hm
  rw [Nat.card_congr (fixedEquiv ρ), hV] at hm
  omega

/-- An order-five actor moves at most four binary dimensions on a module of order 64. -/
theorem quintic_fixedIndex_le_sixteen (ρ : Representation (ZMod 2) A V) [Finite V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 64) : fixedIndex ρ ≤ 16 := by
  have hb := invariant_card ρ hA hV
  have hc := fixedIndex_mul_card ρ
  rw [hV] at hc
  nlinarith

/-- Fixed indices multiply on the literal product representation. -/
theorem fixedIndex_prod (ρ : Representation (ZMod 2) A V)
    (σ : Representation (ZMod 2) A W) [Finite V] [Finite W] :
    fixedIndex (ρ.prod σ) = fixedIndex ρ * fixedIndex σ := by
  let e : (ρ.prod σ).invariants ≃ ρ.invariants × σ.invariants :=
    { toFun := fun x => (⟨x.1.1, fun a => congrArg Prod.fst (x.2 a)⟩,
        ⟨x.1.2, fun a => congrArg Prod.snd (x.2 a)⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1), fun a => Prod.ext (x.1.2 a) (x.2.2 a)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (ρ.prod σ).invariants))
  rw [fixedIndex_mul_card, Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  calc
    Nat.card V * Nat.card W =
        (fixedIndex ρ * Nat.card ρ.invariants) * (fixedIndex σ * Nat.card σ.invariants) := by
      rw [fixedIndex_mul_card, fixedIndex_mul_card]
    _ = _ := by ring

end Representation.BinaryFixedPoints

namespace Subgroup
variable {G : Type*} [Group G]

/-- Fixed points for subgroup conjugation are the literal relative centralizer. -/
theorem fixedPoints_conjugation_eq_centralizer (A R : Subgroup G)
    (hAR : A ≤ normalizer (R : Set G)) :
    let := conjMulDistribMulActionOfLeNormalizer A R hAR
    FixedPoints.subgroup A R = (centralizer (A : Set G)).subgroupOf R := by
  let := conjMulDistribMulActionOfLeNormalizer A R hAR
  ext r
  constructor
  · intro hr
    apply mem_centralizer_iff.mpr
    intro a ha
    have he := congrArg Subtype.val (hr ⟨a, ha⟩)
    change a * (r : G) * a⁻¹ = (r : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hr a
    apply Subtype.ext
    change (a : G) * (r : G) * (a : G)⁻¹ = (r : G)
    have hh := mem_centralizer_iff.mp hr a a.property
    exact mul_inv_eq_iff_eq_mul.mpr hh

/-- Coprime lifting factors a two-group's fixed index through a relative normal quotient. -/
theorem centralizer_relIndex_eq_quotient_mul [Finite G] (A R N : Subgroup G)
    (hR : IsPGroup 2 R) (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hNR : N ≤ R) (hAR : A ≤ normalizer (R : Set G))
    (hAN : A ≤ normalizer (N : Set G)) [(N.subgroupOf R).Normal] :
    let := quotientConjugationAction A R N hAR hAN
    (centralizer (A : Set G)).relIndex R =
      (FixedPoints.subgroup A (R ⧸ N.subgroupOf R)).index *
        (centralizer (A : Set G)).relIndex N := by
  let := conjMulDistribMulActionOfLeNormalizer A R hAR
  let hInv : IsInvariant A R (N.subgroupOf R) :=
    ⟨fun a r => mem_normalizer_iff.mp (hAN a.property) r⟩
  let := quotientMulDistribMulAction (N.subgroupOf R) hInv
  let := hR.isNilpotent
  have hi := FixedPoints.index_eq_quotient_mul_kernel_of_coprime
    (A := A) (V := R) inferInstance hcop (N.subgroupOf R) hInv
  rw [fixedPoints_conjugation_eq_centralizer A R hAR, inf_relIndex_left, relIndex_subgroupOf hNR] at hi
  exact hi

open scoped commutatorElement in
/-- A centralized relative quotient contributes no coprime fixed index. -/
theorem centralizer_relIndex_eq_of_commutator_le [Finite G] (A R N : Subgroup G)
    (hR : IsPGroup 2 R) (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hNR : N ≤ R) (hAR : A ≤ normalizer (R : Set G))
    (hAN : A ≤ normalizer (N : Set G)) [(N.subgroupOf R).Normal]
    (hc : ⁅R,A⁆ ≤ N) :
    (centralizer (A : Set G)).relIndex R = (centralizer (A : Set G)).relIndex N := by
  let := quotientConjugationAction A R N hAR hAN
  have ht : FixedPoints.subgroup A (R ⧸ N.subgroupOf R) = ⊤ := by
    apply top_unique
    intro x _ a
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) x
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (a : G) * (r : G) * (a : G)⁻¹ / (r : G) ∈ N
    rw [commutator_comm] at hc
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      hc (commutator_mem_commutator a.property r.property)
  rw [centralizer_relIndex_eq_quotient_mul A R N hR hcop hNR hAR hAN, ht, index_top, one_mul]

end Subgroup

namespace FixedPoints
variable {A R : Type*} [Group A] [Group R] [Finite R] [MulDistribMulAction A R]

/-- A five-group acting on a two-group of order at most 64 has fixed index at most 16. -/
theorem quintic_index_le_sixteen (hA : IsPGroup 5 A) (hR : IsPGroup 2 R)
    (hcard : Nat.card R ≤ 64) : (subgroup A R).index ≤ 16 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨n, hn⟩ := hR.index (subgroup A R)
  obtain ⟨m, hm⟩ := (hR.to_subgroup (subgroup A R)).exists_card_eq
  have hc := hA.card_modEq_card_fixedPoints R
  change Nat.card R ≡ Nat.card (subgroup A R) [MOD 5] at hc
  rw [← (subgroup A R).index_mul_card] at hc
  have hcop : Nat.Coprime 5 (Nat.card (subgroup A R)) := by
    rw [hm]
    exact (by decide : Nat.Coprime 5 2).pow_right m
  have hi : (subgroup A R).index ≡ 1 [MOD 5] := by
    apply Nat.ModEq.cancel_right_of_coprime hcop
    simpa only [one_mul] using hc
  have hle := (Nat.le_of_dvd (Nat.card_pos (α := R)) (subgroup A R).index_dvd_card).trans hcard
  rw [hn] at hle hi ⊢
  have hnle : n ≤ 6 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  interval_cases n <;> norm_num [Nat.ModEq] at hi <;> norm_num

end FixedPoints
