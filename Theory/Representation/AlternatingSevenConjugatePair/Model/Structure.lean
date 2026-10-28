module

public import Theory.Representation.AlternatingSevenConjugatePair.Model.Natural
public import Theory.Representation.BinaryPrimeDisplacement
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.LinearAlgebra.Determinant

/-!
# Irreducibility and inequivalence of the binary A₇ four-spaces

A faithful four-dimensional binary action of A₇ has no fixed vectors: an
order-five element moves at least four dimensions, since two has order four
modulo five. Simplicity then makes the action on every nonzero invariant
subspace faithful. The same degree bound forces that subspace to be the whole
four-space. This proves irreducibility for both of the actual actions in
`Model.Natural`.

An intertwining equivalence would be an element of SL₄(2), since every nonzero
binary determinant is one. The specified exceptional comparison transports it
to an even permutation implementing odd conjugation on the embedded A₇.
The quotient of the two implementing permutations centralizes A₇. Three explicit
3-cycles show that this centralizer in S₈ is trivial, contradicting their signs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.8, printed p.389/PDF p.400, with standing hypotheses on printed p.377.
The actual A₈–SL₄(2) comparison is the attributed ATLAS port already used by
`Model.Natural`; group orders are used only for the representation degree bound.
-/

public section

open Representation
open scoped MatrixGroups
namespace Representation.AlternatingSevenConjugatePair.Model
noncomputable section

private theorem five_dvd_card : 5 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem faithful_four_irreducible
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hf : Function.Injective ρ) : IsIrreducible ρ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 7)) 5
    five_dvd_card
  have hb := BinaryOffender.prime_order_le_fixedCodim ρ hf
    (by decide : Nat.Prime 5) (by decide) g hg
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hb
  have hz : ρ.invariants = ⊥ := by
    have hdim := BinaryOffender.fixedCodim_add_finrank ρ (Subgroup.zpowers g)
    rw [four_dimension] at hdim
    have hfix : BinaryOffender.fixedSpace ρ (Subgroup.zpowers g) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by omega)
    apply le_antisymm _ bot_le
    intro v hv
    apply hfix.le
    intro a
    exact hv a.val
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hfaith : Function.Injective N.toRepresentation := by
    rcases N.toRepresentation.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact N.toRepresentation.ker_eq_bot_iff.mp hk
    · have he : N.toRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp hk
      have hle : N.toSubmodule ≤ ρ.invariants := by
        intro v hv g
        have h := DFunLike.congr_fun (congrArg (fun σ => σ g) he) ⟨v, hv⟩
        exact congrArg Subtype.val h
      rw [hz] at hle
      exact (hN (Subrepresentation.toSubmodule_injective (le_bot_iff.mp hle))).elim
  have hlo := BinaryPrimeDegree.orderOf_le_finrank N.toRepresentation hfaith
    (by decide : Nat.Prime 5) (by decide : 5 ≠ 2) five_dvd_card
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  apply Subrepresentation.toSubmodule_injective
  by_contra hnt
  have hlt := Submodule.finrank_lt hnt
  rw [four_dimension] at hlt
  omega

/-- The concrete restricted natural binary four-space is irreducible. -/
theorem natural_isIrreducible : IsIrreducible natural :=
  faithful_four_irreducible natural natural_faithful

/-- Its conjugate by the odd transposition is irreducible. -/
theorem outerNatural_isIrreducible : IsIrreducible outerNatural :=
  faithful_four_irreducible outerNatural outerNatural_faithful

private def linearEquivToSL (e : Four ≃ₗ[ZMod 2] Four) : SL(4, ZMod 2) :=
  ⟨LinearMap.toMatrix' e.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ e.isUnit_det'.ne_zero⟩

private theorem linearEquivToSL_apply (e : Four ≃ₗ[ZMod 2] Four) :
    Matrix.SpecialLinearGroup.toLin' (linearEquivToSL e) = e := by
  apply LinearEquiv.toLinearMap_injective
  exact Matrix.toLin'_toMatrix' e.toLinearMap

private abbrev liftPermutation : Equiv.Perm (Fin 7) →* Equiv.Perm (Fin 8) :=
  Equiv.Perm.viaEmbeddingHom letterEmbedding

private theorem liftPermutation_eq (a : Equiv.Perm (Fin 7)) (b : Equiv.Perm (Fin 8))
    (hb : ∀ i : Fin 7, b i.castSucc = (a i).castSucc) (hl : b 7 = 7) :
    liftPermutation a = b := by
  apply _root_.Equiv.ext
  intro x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · change a.viaEmbedding letterEmbedding 7 = b 7
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem, hl]
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val = 7 at hv
    omega
  · exact (Equiv.Perm.viaEmbedding_apply a letterEmbedding i).trans (hb i).symm

private theorem centralizer_embedding (p : Equiv.Perm (Fin 8))
    (hp : ∀ a : alternatingGroup (Fin 7),
      p * (alternatingEmbedding a).val = (alternatingEmbedding a).val * p) : p = 1 := by
  let a : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩
  let b : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 3 * Equiv.swap 0 4, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩
  let c : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 5 * Equiv.swap 0 6, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩
  let a8 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 0 2
  let b8 : Equiv.Perm (Fin 8) := Equiv.swap 0 3 * Equiv.swap 0 4
  let c8 : Equiv.Perm (Fin 8) := Equiv.swap 0 5 * Equiv.swap 0 6
  have ha : (alternatingEmbedding a).val = a8 :=
    liftPermutation_eq a.val a8 (by decide) (by decide)
  have hb : (alternatingEmbedding b).val = b8 :=
    liftPermutation_eq b.val b8 (by decide) (by decide)
  have hc : (alternatingEmbedding c).val = c8 :=
    liftPermutation_eq c.val c8 (by decide) (by decide)
  have hpa : p * a8 = a8 * p := ha ▸ hp a
  have hpb : p * b8 = b8 * p := hb ▸ hp b
  have hpc : p * c8 = c8 * p := hc ▸ hp c
  have ha0 : a8 (p 0) ≠ p 0 := by
    exact Equiv.Perm.mem_support.mp ((Equiv.Perm.mem_support_iff_of_commute hpa 0).mpr (by decide))
  have hb0 : b8 (p 0) ≠ p 0 := by
    exact Equiv.Perm.mem_support.mp ((Equiv.Perm.mem_support_iff_of_commute hpb 0).mpr (by decide))
  -- The first two supports intersect in the single letter zero.
  have h0 : p 0 = 0 :=
    (by decide : ∀ i : Fin 8, a8 i ≠ i → b8 i ≠ i → i = 0) (p 0) ha0 hb0
  -- Commutation propagates that fixed letter around all three cycles.
  have move (q : Equiv.Perm (Fin 8)) (hq : p * q = q * p)
      (i : Fin 8) (hi : p i = i) : p (q i) = q i := by
    simpa only [Equiv.Perm.mul_apply, hi] using congrArg (fun r : Equiv.Perm (Fin 8) => r i) hq
  have h2 : p 2 = 2 := by simpa only [show a8 0 = 2 by decide] using move a8 hpa 0 h0
  have h1 : p 1 = 1 := by simpa only [show a8 2 = 1 by decide] using move a8 hpa 2 h2
  have h4 : p 4 = 4 := by simpa only [show b8 0 = 4 by decide] using move b8 hpb 0 h0
  have h3 : p 3 = 3 := by simpa only [show b8 4 = 3 by decide] using move b8 hpb 4 h4
  have h6 : p 6 = 6 := by simpa only [show c8 0 = 6 by decide] using move c8 hpc 0 h0
  have h5 : p 5 = 5 := by simpa only [show c8 6 = 5 by decide] using move c8 hpc 6 h6
  have h7 : p 7 = 7 := by
    have hn0 := p.injective.ne (by decide : (7 : Fin 8) ≠ 0)
    have hn1 := p.injective.ne (by decide : (7 : Fin 8) ≠ 1)
    have hn2 := p.injective.ne (by decide : (7 : Fin 8) ≠ 2)
    have hn3 := p.injective.ne (by decide : (7 : Fin 8) ≠ 3)
    have hn4 := p.injective.ne (by decide : (7 : Fin 8) ≠ 4)
    have hn5 := p.injective.ne (by decide : (7 : Fin 8) ≠ 5)
    have hn6 := p.injective.ne (by decide : (7 : Fin 8) ≠ 6)
    rw [h0] at hn0
    rw [h1] at hn1
    rw [h2] at hn2
    rw [h3] at hn3
    rw [h4] at hn4
    rw [h5] at hn5
    rw [h6] at hn6
    exact (by intro i; fin_cases i <;> simp : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 →
      i ≠ 4 → i ≠ 5 → i ≠ 6 → i = 7) (p 7) hn0 hn1 hn2 hn3 hn4 hn5 hn6
  apply _root_.Equiv.ext
  intro i
  fin_cases i <;> assumption

private def comparison : alternatingGroup (Fin 8) ≃* SL(4, ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    Atlas.Order20160A8.sl4TwoEquivPSL.symm

private theorem comparison_embedding (a : alternatingGroup (Fin 7)) :
    comparison (alternatingEmbedding a) = linearEmbedding a := rfl

/-- Odd conjugation exchanges inequivalent actual A₇ representations. -/
theorem natural_not_equiv_outerNatural : ¬ Nonempty (natural.Equiv outerNatural) := by
  rintro ⟨e⟩
  let s := linearEquivToSL e.toLinearEquiv
  have hlin (a : alternatingGroup (Fin 7)) :
      s * linearEmbedding a = linearEmbedding (outer a) * s := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_mul, map_mul, linearEquivToSL_apply]
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun (e.isIntertwining' a) v
  let q : alternatingGroup (Fin 8) := comparison.symm s
  have hq (a : alternatingGroup (Fin 7)) :
      q * alternatingEmbedding a = alternatingEmbedding (outer a) * q := by
    apply comparison.injective
    simpa only [map_mul, comparison_embedding, q, MulEquiv.apply_symm_apply] using hlin a
  let t : Equiv.Perm (Fin 8) := liftPermutation transposition
  have ht : t * t = 1 := by
    change liftPermutation transposition * liftPermutation transposition = 1
    rw [← map_mul, ← pow_two, transposition_sq, map_one]
  have hout (a : alternatingGroup (Fin 7)) :
      (alternatingEmbedding (outer a)).val = t * (alternatingEmbedding a).val * t := by
    change liftPermutation (transposition * a.val * transposition) = _
    rw [map_mul, map_mul]
    rfl
  have hcentral : t * q.val = 1 := by
    apply centralizer_embedding
    intro a
    have ha := congrArg Subtype.val (hq a)
    change q.val * (alternatingEmbedding a).val =
      (alternatingEmbedding (outer a)).val * q.val at ha
    rw [hout] at ha
    calc
      (t * q.val) * (alternatingEmbedding a).val =
          t * (q.val * (alternatingEmbedding a).val) := mul_assoc _ _ _
      _ = t * ((t * (alternatingEmbedding a).val * t) * q.val) := by rw [ha]
      _ = (alternatingEmbedding a).val * (t * q.val) := by
        simp only [← mul_assoc, ht, one_mul]
  have heven : q.val.sign = 1 := q.property
  have hodd : t.sign = -1 := by
    change (Equiv.Perm.viaEmbedding transposition letterEmbedding).sign = -1
    rw [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    decide
  have hs := congrArg Equiv.Perm.sign hcentral
  rw [map_mul, hodd, heven, mul_one, map_one] at hs
  exact (by decide : (-1 : ℤˣ) ≠ 1) hs

end
end Representation.AlternatingSevenConjugatePair.Model
