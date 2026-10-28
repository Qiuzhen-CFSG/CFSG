module

public import Glauberman.SylowAutomorphisms.NormalComplement.Contracts
public import Theory.GroupTheory.PrimePowerDecomposition
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct

/-!
# Odd displacement in the normalizer of an abelian Sylow subgroup

If an abelian Sylow two-subgroup P is not central in its normalizer, split a
noncentral normalizer element into its commuting two-power and odd-order parts.
The two-power part belongs to P and centralizes P, so the odd-order part x
still acts nontrivially.

Put D = [P, ⟨x⟩] and take the elements of square one in D. This is precisely
the source subgroup Ω₁(P) ∩ D. Cauchy's theorem makes it nontrivial; coprime
splitting makes D disjoint from the fixed subgroup. The displacement
u ↦ x u x⁻¹ u⁻¹ consequently has trivial kernel on this finite elementary
abelian subgroup and is surjective. All normality is relative to the
normalizer; no normality of P in the ambient group is assumed.

Source: Glauberman, “On the automorphism group of a finite group having no
non-identity normal subgroups of odd order”, Math. Z. 93 (1966),
Theorem 1(b), p.158, and Lemma 3, pp.156–157; DOI 10.1007/BF01111033.
The final theorem supplies the construction input to
`normalComplement_of_displacement_inputs` in the parent assembly module.
-/

public section

namespace Glauberman.SylowAutomorphisms.NormalComplement
open Subgroup
open scoped IsMulCommutative commutatorElement

/-- Failure of centrality in the normalizer of an abelian Sylow two-subgroup
is witnessed by an element of odd order in that same normalizer. -/
theorem exists_odd_actor_of_not_normalizer_le_centralizer {A : Type*} [Group A] [Finite A] (P : Sylow 2 A)
    (habelian : IsMulCommutative P)
    (hnot : ¬ normalizer (P : Set A) ≤ centralizer (P : Set A)) :
    ∃ x : A, Odd (orderOf x) ∧ x ∈ normalizer (P : Set A) ∧
      x ∉ centralizer (P : Set A) := by
  classical
  obtain ⟨g, hgN, hgC⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨u, x, hu, hx, _, hux, huZ, hxZ⟩ :=
    exists_prime_power_decomposition 2 Nat.prime_two g
  have hZN : zpowers g ≤ normalizer (P : Set A) := zpowers_le.mpr hgN
  have huP : u ∈ (P : Subgroup A) := by
    obtain ⟨k, hk⟩ := hu
    have hp : IsPGroup 2 (zpowers u) := IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk)
    have hm : u ∈ zpowers u ⊓ normalizer (P : Set A) := ⟨mem_zpowers u, hZN huZ⟩
    rw [hp.inf_normalizer_sylow P] at hm
    exact hm.2
  have huC : u ∈ centralizer (P : Set A) :=
    (le_centralizer_iff_isMulCommutative.mpr habelian) huP
  refine ⟨x, Nat.coprime_two_left.mp hx, hZN hxZ, ?_⟩
  intro hxC
  exact hgC (hux ▸ (centralizer (P : Set A)).mul_mem huC hxC)

/-- The square-one part of the displacement subgroup of a noncentral odd
normalizer element is nonzero elementary abelian, and displacement is
surjective on it. The last clause identifies the subgroup with the one used
in the source proof. -/
theorem exists_oddDisplacement_of_odd_actor {A : Type*} [Group A] [Finite A] (P : Sylow 2 A)
    (habelian : IsMulCommutative P) (x : A) (hodd : Odd (orderOf x))
    (hxN : x ∈ normalizer (P : Set A)) (hxC : x ∉ centralizer (P : Set A)) :
    ∃ d : OddDisplacement A, d.subgroup ≤ (P : Subgroup A) ∧ d.actor = x ∧
      ∀ u : A, u ∈ d.subgroup ↔ u ∈ ⁅(P : Subgroup A), zpowers x⁆ ∧ u ^ 2 = 1 := by
  let : IsMulCommutative P := habelian
  let X := zpowers x
  let D : Subgroup A := ⁅(P : Subgroup A), X⁆
  have hXN : X ≤ normalizer (P : Set A) := zpowers_le.mpr hxN
  have hDP : D ≤ (P : Subgroup A) := le_normalizer_iff_commutator_le_left.mp hXN
  have hD : D ≠ ⊥ := by
    intro h
    have hcentral : X ≤ centralizer (P : Set A) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
    exact hxC (hcentral (mem_zpowers x))
  have hxD : x ∈ normalizer (D : Set A) :=
    normalizer_commutator_ge_right (P : Subgroup A) X (mem_zpowers x)
  have hcop : Nat.Coprime (Nat.card X) (Nat.card P) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn, Nat.card_zpowers]
    exact hodd.coprime_two_right.pow_right n
  have hdis : Disjoint D ((P : Subgroup A) ⊓ centralizer (X : Set A)) :=
    commutator_disjoint_centralizer_of_coprime (P : Subgroup A) X hXN hcop
  let U : Subgroup A := {
    carrier := {u | u ∈ D ∧ u ^ 2 = 1}
    one_mem' := ⟨D.one_mem, one_pow 2⟩
    mul_mem' := by
      intro a b ha hb
      refine ⟨D.mul_mem ha.1 hb.1, ?_⟩
      have hab : Commute a b := setLike_mul_comm (hDP ha.1) (hDP hb.1)
      rw [hab.mul_pow, ha.2, hb.2, one_mul]
    inv_mem' := by
      intro a ha
      exact ⟨D.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hUD : U ≤ D := fun _ hu => hu.1
  have hUP : U ≤ (P : Subgroup A) := hUD.trans hDP
  have hU : U ≠ ⊥ := by
    have hpg : IsPGroup 2 D := P.isPGroup'.to_le hDP
    have hcard : 2 ∣ Nat.card D := hpg.card_eq_or_dvd.resolve_left (by
      simpa only [Subgroup.card_eq_one] using hD)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hcard
    have hum : (u : A) ∈ U := ⟨u.property, by
      have hh : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
      exact congrArg Subtype.val hh⟩
    intro hbot
    have hone : (u : A) = 1 := by simpa only [hbot, mem_bot] using hum
    have : u = 1 := Subtype.ext hone
    simp [this] at hu
  have hUE : IsElementaryAbelian 2 U := {
    toIsMulCommutative := .of_setLike_mul_comm fun _ ha _ hb =>
      setLike_mul_comm (hUP ha) (hUP hb)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun u =>
      Subtype.ext u.property.2 }
  let := hUE
  have hxU : x ∈ normalizer (U : Set A) := by
    apply mem_normalizer_fintype
    intro u hu
    refine ⟨(mem_normalizer_iff.mp hxD u).mp hu.1, ?_⟩
    have hh := congrArg (MulAut.conj x) hu.2
    simpa only [map_pow, map_one, MulAut.conj_apply] using hh
  let φ : MulAut U := U.normalizerMonoidHom ⟨x, hxU⟩
  let δ : U →* U := {
    toFun := fun u => φ u * u⁻¹
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [map_mul, mul_inv_rev]
      ac_rfl }
  have hinj : Function.Injective δ := by
    apply (injective_iff_map_eq_one δ).mpr
    intro u hu
    have hfix : φ u = u := mul_inv_eq_one.mp hu
    have hcomm : x * (u : A) = (u : A) * x := by
      have hh := congrArg (fun v : U => (v : A)) hfix
      change x * (u : A) * x⁻¹ = u at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp hdis (hUD u.property)
    refine ⟨hUP u.property, ?_⟩
    rw [show X = zpowers x from rfl, zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hcomm.symm
  have hsurj : ∀ u ∈ U, ∃ v ∈ U, x * v * x⁻¹ * v⁻¹ = u := by
    intro u hu
    obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj (⟨u, hu⟩ : U)
    exact ⟨v, v.property, congrArg Subtype.val hv⟩
  exact ⟨⟨x, hodd, U, hU, hUE, hxU, hsurj⟩, hUP, rfl, fun _ => Iff.rfl⟩


/-- The complete normalizer construction in Glauberman's Theorem 1(b).
This discharges the construction input of the normal-complement assembly;
the independent fusion exclusion remains with that assembly's owner. -/
theorem exists_oddDisplacement_of_not_normalizer_le_centralizer
    {A : Type*} [Group A] [Finite A] (P : Sylow 2 A)
    (habelian : IsMulCommutative P)
    (hnot : ¬ normalizer (P : Set A) ≤ centralizer (P : Set A)) :
    ∃ d : OddDisplacement A,
      d.subgroup ≤ (P : Subgroup A) ∧ d.actor ∈ normalizer (P : Set A) := by
  obtain ⟨x, hodd, hxN, hxC⟩ :=
    exists_odd_actor_of_not_normalizer_le_centralizer P habelian hnot
  obtain ⟨d, hdP, hdx, _⟩ := exists_oddDisplacement_of_odd_actor P habelian x hodd hxN hxC
  exact ⟨d, hdP, hdx.symm ▸ hxN⟩

end Glauberman.SylowAutomorphisms.NormalComplement
