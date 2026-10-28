module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Minimal
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.ChiefFactorDirectPower
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.IsPerfect

/-!
# The nonsolvable minimal normal actor in 15.3.58

Minimal normality makes the actor characteristically simple, and nonsolvability
makes its characteristic commutator subgroup the whole group. The finite
characteristically-simple theorem gives an actual simple-subgroup direct power.
Projection to a coordinate makes the simple factor perfect and nonabelian.
Cauchy's theorem supplies an odd-prime element in that factor: otherwise it
would be a two-group. Taking its cyclic subgroup in every coordinate gives
an elementary abelian subgroup of order `p^n`, bounding `n` by the odd prime
rank. Strong quasithinness therefore leaves precisely one or two factors.

Perfectness also kills every prime-power quotient, so the two-residual here
is `pResidual 2 K`, and is all of `K`; it is not the two-core.
Nonsolvability remains the explicit contract supplied by the independent
solvable-case exclusion in the parent proof.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149,
proof of 15.3.58. The structure theorem is the one cited in E.1.10(5).
-/

@[expose] public section

open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

/-- A nonsolvable minimal normal subgroup is perfect. -/
theorem IsMinimalNormal.isPerfect_of_not_isSolvable {G : Type*} [Group G] (K : Subgroup G)
    (hK : IsMinimalNormal K) (hns : ¬ Group.IsSolvable K) : Group.IsPerfect K := by
  let := hK.1
  obtain hb | ht := ChiefFactor.characteristic_eq_bot_or_top_of_minimal_normal
    K hK.2.2 (commutator K) inferInstance
  · let := (_root_.commutator_eq_bot_iff K).mp hb
    exact False.elim (hns inferInstance)
  · exact ⟨ht⟩

private theorem residual_eq_top_of_perfect {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (p : ℕ) [Fact p.Prime] : pResidual p G = ⊤ := by
  apply (pResidual_eq_top_iff p G).mpr
  intro N hN hp
  let := hN
  have hs : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem exists_odd_prime_element_of_not_isSolvable {S : Type*} [Group S] [Finite S] (hns : ¬ Group.IsSolvable S) :
    ∃ (p : ℕ) (x : S), p.Prime ∧ Odd p ∧ orderOf x = p := by
  by_contra! hn
  have hp : IsPGroup 2 S := by
    apply IsPGroup.of_card_dvd_pow (n := Nat.card S)
    apply (Nat.dvd_pow_self_iff (Nat.card_pos.ne') (by decide : 2 ≠ 0)).mpr
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    by_cases he : p = 2
    · simp [he, Nat.prime_two]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hp := ⟨hpp⟩) hpd
    exact False.elim (hn p x hpp (hpp.odd_of_ne_two he) hx)
  let := hp.isNilpotent
  exact hns inferInstance

private theorem primeRank_directPower_ge_of_prime_order {S : Type*} [Group S] [Finite S] {n p : ℕ} [Fact p.Prime]
    (x : S) (hx : orderOf x = p) : n ≤ primeRank p (Fin n → S) := by
  let C := zpowers x
  let : IsElementaryAbelian p C := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hx ▸ pow_orderOf_eq_one x)
  let f : (Fin n → C) →* (Fin n → S) := MonoidHom.piMap (fun _ => C.subtype)
  have hf : Function.Injective f := by
    intro a b h
    funext i
    exact Subtype.ext (congrFun h i)
  let E := f.range
  let e : (Fin n → C) ≃* E := MonoidHom.ofInjective hf
  let : IsElementaryAbelian p E := {
    toIsMulCommutative := ⟨⟨by
      intro a b
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, mul_comm]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      obtain ⟨a, rfl⟩ := e.surjective a
      rw [← map_pow]
      convert e.map_one using 1
      congr 1
      funext i
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p C) (a i)) }
  apply IsElementaryAbelian.primeRank_ge_of_card E
  calc
    Nat.card E = Nat.card (Fin n → C) := Nat.card_congr e.symm.toEquiv
    _ = p ^ n := by simp [Nat.card_fun, C, Nat.card_zpowers, hx]

/-- A nonsolvable minimal normal strongly-quasithin subgroup is an actual
power of one of its nonabelian simple subgroups, with one or two factors. -/
theorem IsMinimalNormal.exists_simple_power {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK : IsMinimalNormal K) (hns : ¬ Group.IsSolvable K)
    (hqt : IsStronglyQuasithin K) :
    ∃ S : Subgroup K, IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧
      ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nonempty (K ≃* (Fin n → S)) := by
  let := hK.1
  let : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hK.2.1
  let := hK.isPerfect_of_not_isSolvable K hns
  obtain ⟨S, hS, n, hn, ⟨e⟩⟩ := CharacteristicallySimple.exists_simple_subgroup_power
    (ChiefFactor.characteristic_eq_bot_or_top_of_minimal_normal K hK.2.2)
  let := hS
  let f : K →* S := (Pi.evalMonoidHom (fun _ : Fin n => S) ⟨0, hn⟩).comp e.toMonoidHom
  have hf : Function.Surjective f := by
    intro s
    exact ⟨e.symm (fun _ => s), by simp [f]⟩
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective hf
  have hna := Group.IsPerfect.not_isMulCommutative S
  obtain ⟨p, x, hp, ho, hx⟩ :=
    exists_odd_prime_element_of_not_isSolvable (Group.IsPerfect.not_isSolvable S)
  let : Fact p.Prime := ⟨hp⟩
  have hle : n ≤ 2 := (primeRank_directPower_ge_of_prime_order x hx).trans
    ((IsStronglyQuasithin.equiv e).mp hqt p hp ho)
  exact ⟨S, hS, hna, n, by omega, ⟨e⟩⟩

/-- The genuine two-residual of the nonsolvable minimal normal subgroup is whole. -/
theorem IsMinimalNormal.twoResidual_eq_top {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hK : IsMinimalNormal K) (hns : ¬ Group.IsSolvable K) :
    pResidual 2 K = ⊤ := by
  let := hK.isPerfect_of_not_isSolvable K hns
  exact residual_eq_top_of_perfect 2

/-- Embedding the intrinsic two-residual back into the actor recovers `K`. -/
theorem IsMinimalNormal.map_twoResidual_eq_self {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hK : IsMinimalNormal K) (hns : ¬ Group.IsSolvable K) :
    (pResidual 2 K).map K.subtype = K := by
  rw [hK.twoResidual_eq_top K hns, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- SQTK supplies the same direct-power conclusion and places the actual simple
subgroup in the full input class, without replacing it by a group-family tag. -/
theorem IsMinimalNormal.exists_simple_power_of_sqtk
    {G : Type*} [Group G] [Finite G] {C : GroupClass}
    (hG : IsSQTK C G) (K : Subgroup G)
    (hK : IsMinimalNormal K) (hns : ¬ Group.IsSolvable K) :
    ∃ S : Subgroup K, IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧ C S ∧
      ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nonempty (K ≃* (Fin n → S)) := by
  obtain ⟨S, hS, hna, n, hn, he⟩ :=
    hK.exists_simple_power K hns (hG.stronglyQuasithin.subgroup K)
  exact ⟨S, hS, hna, (hG.isKGroup.subgroup K) S hS S
    (MonoidHom.id S) Function.surjective_id, n, hn, he⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
