module

public import Theory.Alternating.Aut
public import Theory.GroupAction.AutomorphismFixedTransport
import Mathlib.Tactic.NormNum

/-!
# Sylow four-groups and their fixed automorphisms in A₅

The standard double transpositions generate a Sylow four-group. The proved
symmetric-group description of Aut(A₅) identifies its pointwise fixer with
inner automorphisms by that four-group. Sylow conjugacy gives the result for
any Sylow subgroup.

A short permutation calculation also shows that a subgroup normalized by a
Sylow four-group and having no nonidentity element of order five normalizes
the four-group. This is the local calculation behind the PSL₂(5) quotient
action in Aschbacher–Smith 15.4.20, printed p.1164; the actual PSL₂(5) ≃ A₅
comparison is assembled in the parent module. All finite calculations use
kernel reduction.
-/

open Subgroup
namespace Theory.PSL2.SylowFixedQuotients
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)
private def a : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def b : A5 := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def four : Subgroup A5 := centralizer ({a} : Set A5) ⊓ centralizer ({b} : Set A5)
private instance fourDecidable : DecidablePred (· ∈ four) := fun x =>
  decidable_of_iff (x * a = a * x ∧ x * b = b * x) (by
    simp only [four, mem_inf, mem_centralizer_singleton_iff])
private theorem a_mem : a ∈ four := by decide +kernel
private theorem b_mem : b ∈ four := by decide +kernel
private theorem four_card : Nat.card four = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem card_a5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]
private theorem commutes_even : ∀ σ : S5,
    σ * (a : S5) = (a : S5) * σ → σ * (b : S5) = (b : S5) * σ →
    σ ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private noncomputable def fourSylow : Sylow 2 A5 := Sylow.ofCard four (by
  rw [four_card, card_a5]
  rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl)

private theorem four_fixed_inner (β : MulAut A5)
    (hβ : ∀ x ∈ four, β x = x) : ∃ x ∈ four, β = MulAut.conj x := by
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide)
      (by decide)).2 β
  have hcomm (x : A5) (hx : x ∈ four) : σ * x.val = x.val * σ := by
    have h := congrArg Subtype.val (hβ x hx)
    change σ * x.val * σ⁻¹ = x.val at h
    exact mul_inv_eq_iff_eq_mul.mp h
  let c : A5 := ⟨σ, commutes_even σ (hcomm a a_mem) (hcomm b b_mem)⟩
  refine ⟨c, ?_, ?_⟩
  · exact ⟨mem_centralizer_singleton_iff.mpr (Subtype.ext (hcomm a a_mem)),
      mem_centralizer_singleton_iff.mpr (Subtype.ext (hcomm b b_mem))⟩
  · ext x
    rfl

/-- Transport pointwise-fixer innerness along an actual group isomorphism. -/
public theorem fixed_inner_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (P : Subgroup G)
    (h : ∀ β : MulAut H, (∀ x ∈ P.map e.toMonoidHom, β x = x) →
      ∃ x ∈ P.map e.toMonoidHom, β = MulAut.conj x)
    (β : MulAut G) (hβ : ∀ x ∈ P, β x = x) :
    ∃ x ∈ P, β = MulAut.conj x := by
  obtain ⟨y, hy, he⟩ := h (MulAut.congr e β) (by
    rintro _ ⟨x, hx, rfl⟩
    change e (β (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hβ x hx])
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x, hx, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj]
  exact he

/-- Every automorphism of A₅ fixing a Sylow two-subgroup pointwise is
conjugation by an element of that Sylow subgroup. -/
public theorem alternating_sylow_fixed_inner (P : Sylow 2 A5) (β : MulAut A5)
    (hβ : ∀ x ∈ P, β x = x) : ∃ x ∈ P, β = MulAut.conj x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 P fourSylow
  have he : (P : Subgroup A5).map (MulAut.conj g).toMonoidHom = four := by
    have hh := congrArg (fun Q : Sylow 2 A5 => (Q : Subgroup A5)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    exact hh
  apply fixed_inner_transport (MulAut.conj g) (P : Subgroup A5) ?_ β hβ
  rw [he]
  exact four_fixed_inner

/-- The Sylow two-subgroups of A₅ have order four. -/
public theorem alternating_sylow_card (P : Sylow 2 A5) : Nat.card P = 4 := by
  exact (Nat.card_congr (P.equiv fourSylow).toEquiv).trans four_card

private theorem normalized_four_certificate : ∀ d : A5,
    (∀ p ∈ four, d * (p * d * p⁻¹) ≠ 1 → (d * (p * d * p⁻¹)) ^ 5 ≠ 1) →
    ∀ p ∈ four, d * p * d⁻¹ ∈ four := by
  decide +kernel

private theorem four_normalizes_iff (D : Subgroup A5)
    (hD : ∀ d ∈ D, d ^ 5 = 1 → d = 1)
    (hn : four ≤ normalizer (D : Set A5)) : D ≤ normalizer (four : Set A5) := by
  apply le_normalizer_iff.mpr
  intro d hd
  apply normalized_four_certificate d
  intro p hp hne hpow
  exact hne (hD _ (D.mul_mem hd ((hn hp d).mp hd)) hpow)

/-- In A₅, a subgroup without elements of order five which is normalized
by a Sylow two-subgroup normalizes that Sylow subgroup in return. -/
public theorem alternating_mutual_normalizes_of_no_five (P : Sylow 2 A5) (D : Subgroup A5)
    (hD : ∀ d ∈ D, d ^ 5 = 1 → d = 1)
    (hn : (P : Subgroup A5) ≤ normalizer (D : Set A5)) :
    D ≤ normalizer (P : Set A5) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 P fourSylow
  let e := MulAut.conj g
  have he : (P : Subgroup A5).map e.toMonoidHom = four := by
    have hh := congrArg (fun Q : Sylow 2 A5 => (Q : Subgroup A5)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    exact hh
  have hn' : four ≤ normalizer (D.map e.toMonoidHom : Set A5) := by
    rw [← he, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hn
  have hD' : ∀ d ∈ D.map e.toMonoidHom, d ^ 5 = 1 → d = 1 := by
    rintro _ ⟨d, hd, rfl⟩ hpow
    change (e d) ^ 5 = 1 at hpow
    have hd5 : d ^ 5 = 1 := e.injective (by simpa only [map_pow, map_one] using hpow)
    rw [hD d hd hd5, map_one]
  have hh := four_normalizes_iff (D.map e.toMonoidHom) hD' hn'
  rw [← he, ← Subgroup.map_equiv_normalizer_eq] at hh
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp hh

end Theory.PSL2.SylowFixedQuotients
