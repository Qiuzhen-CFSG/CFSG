module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.NormalClosure
public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic

/-!
# Radical exclusion and coefficient cyclicity

A nontrivial abelian normal subgroup in a faithful primitive action is
regular. At prime-power degree its order therefore puts it in the p-core.
The last nontrivial derived subgroup of a nontrivial solvable radical would
give just such a subgroup. This proves the radical exclusion without a
minimal-counterexample assumption or a regular-subgroup classification.

The literal two-point stabilizer embeds in the finite field's cyclic
automorphism group. An odd prime divisor of its order can consequently be
chosen once the separate two-group exclusion has been established.

Source: GLS, Volume 4, Chapter 1, Lemma 3.8(a) and the choice preceding
Lemma 3.9, `refs/KGroup/GLS4/Chapter1.tex`, lines 419–435.
-/

public section

open scoped IsMulCommutative

namespace MulAction

/-- A faithful primitive action of prime-power degree with trivial p-core
has trivial solvable radical. -/
theorem solvableRadical_eq_bot_of_prime_power_degree
    {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω] [FaithfulSMul X Ω]
    [IsPreprimitive X Ω] {p n : ℕ} [Fact p.Prime]
    (hΩ : Nat.card Ω = p ^ n) (a : Ω) (hcore : pCore p X = ⊥) :
    Subgroup.solvableRadical X = ⊥ := by
  apply Subgroup.solvableRadical_eq_bot_iff_abelian_characteristic_eq_bot.mpr
  intro A hAchar hAcomm
  let := hAchar
  let := hAcomm
  by_contra hA
  let : IsPretransitive A Ω := Atlas.GroupTheory.normal_pretransitive A hA
  have hinj : Function.Injective (fun u : A => (u : X) • a) := by
    intro u v huv
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := Ω)
    intro x
    obtain ⟨w, rfl⟩ := exists_smul_eq A a x
    change u • (w • a) = v • (w • a)
    calc
      u • (w • a) = w • (u • a) := by rw [← mul_smul, mul_comm u w, mul_smul]
      _ = w • (v • a) := congrArg (fun z : Ω => w • z) huv
      _ = v • (w • a) := by rw [← mul_smul, mul_comm w v, mul_smul]
  have hcard : Nat.card A = p ^ n :=
    (Nat.card_eq_of_bijective _ ⟨hinj, fun x => exists_smul_eq A a x⟩).trans hΩ
  have hle : A ≤ pCore p X := le_sSup ⟨inferInstance, IsPGroup.of_card hcard⟩
  exact hA (eq_bot_iff.mpr (hcore ▸ hle))

namespace SemilinearPointStabilizer

variable {X F : Type*} [Group X] [Field F] [MulAction X F] [FaithfulSMul X F]

/-- Lemma 3.8(a) for the actual action, from the original two-core hypothesis. -/
theorem solvableRadical_eq_bot [Finite X] {n : ℕ}
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 2 ^ n)
    (hcore : pCore 2 X = ⊥) : Subgroup.solvableRadical X = ⊥ := by
  let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
  exact MulAction.solvableRadical_eq_bot_of_prime_power_degree hF (0 : F) hcore

namespace Coordinates

variable (c : Coordinates X F)

include c

/-- The scalar subgroup is the actual cyclic image of the field units. -/
theorem scalarSubgroup_isCyclic [Finite F] : IsCyclic c.scalarSubgroup :=
  isCyclic_of_surjective c.scalar.rangeRestrict c.scalar.rangeRestrict_surjective

/-- The literal scalar embedding identifies the order of K. -/
theorem card_scalarSubgroup [Finite F] :
    Nat.card c.scalarSubgroup = Nat.card F - 1 := by
  change Nat.card c.scalar.range = Nat.card F - 1
  rw [← Nat.card_congr (MonoidHom.ofInjective c.scalar_injective).toEquiv,
    Nat.card_units]

/-- The faithful coefficient action realizes Γ as a cyclic group. -/
theorem twoPoint_isCyclic [Finite F] : IsCyclic (twoPoint (X := X) (F := F)) := by
  let p := ringChar F
  have hp : p.Prime := CharP.char_is_prime F p
  let : Fact p.Prime := ⟨hp⟩
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) := {
    toFun σ := AlgEquiv.ofRingEquiv (f := σ) (by
      intro x
      have hh : σ.toRingHom.comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun hh x)
    invFun σ := σ.toRingEquiv
    left_inv σ := by ext x; rfl
    right_inv σ := by ext x; rfl
    map_mul' σ τ := by ext x; rfl }
  let : IsCyclic (F ≃+* F) := e.isCyclic.mpr inferInstance
  exact isCyclic_of_injective c.fieldAut c.fieldAut_injective

/-- The source actor is nonsolvable under the original action hypotheses. -/
theorem not_isSolvable [Finite X] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 2 ^ n)
    (hcore : pCore 2 X = ⊥) : ¬ Group.IsSolvable X := by
  intro hsolv
  let := hsolv
  have hrad := solvableRadical_eq_bot htwo hF hcore
  have htop : (⊤ : Subgroup X) ≤ Subgroup.solvableRadical X :=
    Subgroup.le_solvableRadical ⊤ inferInstance inferInstance
  have hK : c.scalarSubgroup = ⊥ :=
    eq_bot_iff.mpr (le_top.trans (hrad ▸ htop))
  apply c.scalarSubgroup_ne_bot _ hK
  rw [hF]
  have hfour : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  omega

end Coordinates

omit [FaithfulSMul X F] in
/-- The arithmetic choice used before Lemma 3.9. The two-group exclusion
remains a separate source argument. -/
theorem exists_odd_prime_dvd_twoPoint [Finite X]
    (hΓ : ¬ IsPGroup 2 (twoPoint (X := X) (F := F))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (twoPoint (X := X) (F := F)) := by
  classical
  by_contra h
  apply hΓ
  rw [isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)]
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hdvd := (Nat.mem_primeFactors.mp hp).2.1
  have hp2 : p = 2 := by
    by_contra hp2
    exact h ⟨p, hprime, hprime.odd_of_ne_two hp2, hdvd⟩
  subst p
  simp [Nat.prime_two]

end SemilinearPointStabilizer
end MulAction
