module
public import Theory.SpecificGroups.PSL3.QuadraticThreeSylow
public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.Representation.GeneralLinearNatural
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Nonsplit odd-prime rank in ternary linear groups

For a nondefining prime which does not divide the split torus order,
every Sylow subgroup of SL₃ is cyclic. If it divides q²−1, the actual
quadratic torus has prime-to-p index. Otherwise the multiplicative order
of q modulo p is at least three; the faithful natural action embeds the
Sylow subgroup into the units of its finite endomorphism field. Passing
through the literal scalar quotient bounds the prime rank of PSL₃ by one.

This is the rank restriction in Aschbacher–Smith A.3.18, pp.51–53,
used in the noncubic component argument of original 4.3.12(2), p.617.
The source application is in NonblockEndgameSieveModelsNoncubic.
-/

public section
open Subgroup
open scoped MatrixGroups
noncomputable section
namespace Matrix.PSL3.NonsplitPrimeRank
variable (F : Type*) [Field F] [Finite F]

private theorem cyclic_sylow_of_cyclic_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (C : Subgroup G) [IsCyclic C]
    (hi : ¬ p ∣ C.index) (P : Sylow p G) : IsCyclic P := by
  let T : Sylow p C := default
  let A := (T : Subgroup C).map C.subtype
  have ha : IsPGroup p A := T.isPGroup'.map C.subtype
  have hai : ¬ p ∣ A.index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul T.not_dvd_index hi
  let U : Sylow p G := ha.toSylow hai
  let e := (T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  have hc : IsCyclic U := e.isCyclic.mp inferInstance
  exact (U.equiv P).isCyclic.mp hc

private theorem quadratic_torus (r : ℕ) [Fact r.Prime] [CharP F r] :
    ∃ C : Subgroup SL(3,F), IsCyclic C ∧
      C.index = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) := by
  let E := FiniteField.Extension F r 2
  obtain ⟨ρ, _, hρ, _⟩ := Matrix.GeneralLinearGroup.exists_finite_quadratic_torus F r
  let f : Eˣ →* SL(3,F) := (Matrix.SL3.blockEmbedding F).comp ρ
  have hf : Function.Injective f := (Matrix.SL3.blockEmbedding_injective F).comp hρ
  let e : Eˣ ≃* f.range := MonoidHom.ofInjective hf
  have hc : Nat.card f.range = Nat.card F ^ 2 - 1 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_units]
    exact congrArg (fun n => n - 1) (FiniteField.natCard_extension F r 2)
  refine ⟨f.range, e.isCyclic.mp inferInstance, ?_⟩
  have horder : Nat.card SL(3,F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
      Atlas.ExceptionalSupport.card_sl_center]
    exact LinearThree.card_projective_mul_scalar F
  rw [← f.range.card_mul_index, hc] at horder
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F ^ 2 - 1 by
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (Finite.one_lt_card (α := F)) (by decide)))
  rw [horder]
  ring

private theorem cast_pow_eq_one_iff {p k : ℕ} [Fact p.Prime] :
    (Nat.card F : ZMod p) ^ k = 1 ↔ p ∣ Nat.card F ^ k - 1 := by
  have hq : 1 ≤ Nat.card F ^ k := Nat.one_le_pow _ _ Nat.card_pos
  rw [← sub_eq_zero, ← Nat.cast_pow, ← Nat.cast_one,
    ← Nat.cast_sub hq, ZMod.natCast_eq_zero_iff]

private theorem order_ge_three {p : ℕ} [Fact p.Prime]
    (hq : ¬ p ∣ Nat.card F) (hquad : ¬ p ∣ Nat.card F ^ 2 - 1) :
    3 ≤ orderOf (Nat.card F : ZMod p) := by
  have hz : (Nat.card F : ZMod p) ≠ 0 := by
    simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using hq
  have hpos : 0 < orderOf (Nat.card F : ZMod p) :=
    (isOfFinOrder_iff_isUnit.mpr (isUnit_iff_ne_zero.mpr hz)).orderOf_pos
  have htwo : orderOf (Nat.card F : ZMod p) ≠ 2 := by
    intro he
    exact hquad ((cast_pow_eq_one_iff F).mp (he ▸ pow_orderOf_eq_one (Nat.card F : ZMod p)))
  have hone : orderOf (Nat.card F : ZMod p) ≠ 1 := by
    intro he
    apply hquad
    apply (cast_pow_eq_one_iff F).mp
    rw [orderOf_eq_one_iff.mp he, one_pow]
  omega

/-- Every nonsplit nondefining Sylow subgroup of SL₃ is cyclic. -/
theorem special_sylow_isCyclic (r : ℕ) [Fact r.Prime] [CharP F r]
    {p : ℕ} [Fact p.Prime] (hpq : ¬ p ∣ Nat.card F)
    (hpF : (p : F) ≠ 0) (hsplit : ¬ p ∣ Nat.card F - 1)
    (P : Sylow p SL(3,F)) : IsCyclic P := by
  by_cases hquad : p ∣ Nat.card F ^ 2 - 1
  · obtain ⟨C, hC, hi⟩ := quadratic_torus F r
    let := hC
    apply cyclic_sylow_of_cyclic_index C ?_ P
    rw [hi]
    refine (Fact.out : p.Prime).not_dvd_mul
      (fun hd => hpq ((Fact.out : p.Prime).dvd_of_dvd_pow hd)) ?_
    intro hcub
    have h2 := (cast_pow_eq_one_iff F).mpr hquad
    have h3 := (cast_pow_eq_one_iff F).mpr hcub
    have h1 : (Nat.card F : ZMod p) = 1 := by
      simpa only [pow_succ, h2, one_mul] using h3
    exact hsplit (by simpa only [pow_one] using
      (cast_pow_eq_one_iff (k := 1) F).mp (by simpa using h1))
  · let : Fintype F := Fintype.ofFinite F
    let f : P →* GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL.comp (P : Subgroup SL(3,F)).subtype
    have hf : Function.Injective f :=
      Matrix.SpecialLinearGroup.toGL_injective.comp (P : Subgroup SL(3,F)).subtype_injective
    apply Representation.CyclotomicPrimeCyclicity.isCyclic_of_minimal_degree
      P.isPGroup' hpF (by simpa only [Nat.card_eq_fintype_card] using hpq)
      ((Representation.generalLinearNatural 3).comp f)
      ((Representation.generalLinearNatural_injective 3).comp hf)
    simpa only [Module.finrank_pi, Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fin] using
      order_ge_three F hpq hquad

/-- A nonsplit nondefining prime has rank at most one in the actual projective quotient. -/
theorem projective_rank_le_one (r : ℕ) [Fact r.Prime] [CharP F r]
    {p : ℕ} [Fact p.Prime] (hpq : ¬ p ∣ Nat.card F)
    (hpF : (p : F) ≠ 0) (hsplit : ¬ p ∣ Nat.card F - 1) :
    primeRank p PSL(3,F) ≤ 1 := by
  let P : Sylow p SL(3,F) := default
  exact P.primeRank_le_one_of_surjective
    (special_sylow_isCyclic F r hpq hpF hsplit P) (projection F) (projection_surjective F)
end Matrix.PSL3.NonsplitPrimeRank
