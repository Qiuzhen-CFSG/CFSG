module

public import Theory.GroupTheory.PGroup.SupercriticalExistence.ClassTwoOmega
public import Theory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# First omega when roots in the derived subgroup are central

In a finite odd-prime p-group, centrality of the p-th roots in the derived
subgroup forces the first omega subgroup to have exponent dividing p.
Induct on the group order. A root x either generates the whole group or lies
in a maximal subgroup M, which is normal. By induction, first omega in M
has exponent dividing p; its characteristic image is normal in the ambient
group. Thus every commutator of x has order dividing p and is central.
The first omega subgroup consequently has class at most two, so (23.11)
provides the exponent bound.

This supplies the exponent argument of Aschbacher, *Finite Group Theory*,
Second Edition, (23.16), printed p.112. The induction through maximal normal
subgroups replaces the source's minimal two-generator counterexample.
-/

open Subgroup
open scoped commutatorElement

private theorem commutator_closure_le_center_of_generators
    {G : Type*} [Group G] (S : Set G)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ center G) :
    ⁅closure S, closure S⁆ ≤ center G := by
  let q := QuotientGroup.mk' (center G)
  have hc : IsMulCommutative ((closure S).map q) := by
    rw [MonoidHom.map_closure]
    apply isMulCommutative_closure
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hS x hx y hy)
  have heq : (⁅closure S, closure S⁆).map q = ⊥ := by
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.mpr hc
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp heq

private theorem derived_roots_inherit {G : Type*} [Group G] {p : ℕ}
    (h : ∀ z : G, z ∈ _root_.commutator G → z ^ p = 1 → z ∈ center G)
    (M : Subgroup G) :
    ∀ z : M, z ∈ _root_.commutator M → z ^ p = 1 → z ∈ center M := by
  intro z hz hp
  have hm : (z : G) ∈ ⁅M, M⁆ := by
    simpa only [map_subtype_commutator, Subgroup.coe_subtype] using mem_map_of_mem M.subtype hz
  have hc := h z (commutator_mono le_top le_top hm) (congrArg Subtype.val hp)
  exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hc y))

private theorem omega_exponent_of_derived_roots_aux
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    ∀ {G : Type*} [Group G] [Finite G], Nat.card G = n → IsPGroup p G →
      (∀ z : G, z ∈ _root_.commutator G → z ^ p = 1 → z ∈ center G) →
      Monoid.exponent (omega₁ G (p := p)) ∣ p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard hG hroots
    classical
    let X := omega₁ G (p := p)
    have hcomm (x y : G) (hx : x ^ p = 1) :
        ⁅x, y⁆ ∈ center G := by
      by_cases hgen : zpowers x = ⊤
      · have hyx : y ∈ zpowers x := hgen ▸ mem_top y
        have hc : Commute x y := ((zpowers x).le_centralizer (mem_zpowers x) y hyx).symm
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hc.eq]
        exact (center G).one_mem
      · obtain ⟨M, hmax, hxM⟩ := (eq_top_or_exists_le_coatom (zpowers x)).resolve_left hgen
        let : Group.IsNilpotent G := hG.isNilpotent
        let : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
          Group.normalizerCondition_of_isNilpotent hmax
        have hlt : Nat.card M < n := by
          rw [← hcard]
          obtain ⟨a, ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hmax.ne_top)
          exact Finite.card_subtype_lt ha.2
        have hMexp : Monoid.exponent (omega₁ M (p := p)) ∣ p :=
          ih (Nat.card M) hlt rfl (hG.to_subgroup M) (derived_roots_inherit hroots M)
        let W := (omega₁ M (p := p)).map M.subtype
        let : (omega₁ M (p := p)).Characteristic := omega₁_characteristic M
        let : W.Normal := ConjAct.normal_of_characteristic_of_normal
        have hxW : x ∈ W := by
          refine ⟨⟨x, hxM (mem_zpowers x)⟩, subset_closure ?_, rfl⟩
          exact Subtype.ext (by simpa using hx)
        have hcW : ⁅x, y⁆ ∈ W :=
          commutator_le_left W ⊤ (commutator_mem_commutator hxW (mem_top y))
        obtain ⟨c, hc, he⟩ := hcW
        have hcp : ⁅x, y⁆ ^ p = 1 := by
          rw [← he]
          exact congrArg (fun a : omega₁ M (p := p) => ((a : M) : G))
            (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hMexp ⟨c, hc⟩)
        exact hroots _ (commutator_mem_commutator (mem_top x) (mem_top y)) hcp
    have hXX : ⁅X, X⁆ ≤ center G := by
      apply commutator_closure_le_center_of_generators
      intro x hx y _
      exact hcomm x y (by simpa using hx)
    have hclass : _root_.commutator X ≤ center X := by
      intro z hz
      have hm : (z : G) ∈ ⁅X, X⁆ := by
        simpa only [map_subtype_commutator, Subgroup.coe_subtype] using mem_map_of_mem X.subtype hz
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hXX hm) y))
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro z
    apply Subtype.ext
    change (z : G) ^ p = 1
    refine closure_induction (p := fun w _ => w ^ p = 1) ?_ (one_pow p) ?_ ?_ z.property
    · intro w hw
      simpa using hw
    · intro x y hx hy ihx ihy
      exact congrArg Subtype.val (mul_pow_eq_one_of_class_two hp hclass
        (x := (⟨x, hx⟩ : X)) (y := (⟨y, hy⟩ : X)) (Subtype.ext ihx) (Subtype.ext ihy))
    · intro x hx ih
      rw [inv_pow, ih, inv_one]

/-- Central p-th roots in the derived subgroup suffice for first omega to
have exponent dividing the odd prime p. -/
public theorem IsPGroup.exponent_omega_one_dvd_of_derived_prime_roots_central
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (hp : p ≠ 2)
    (hroots : ∀ z : G, z ∈ _root_.commutator G → z ^ p = 1 → z ∈ center G) :
    Monoid.exponent (omega₁ G (p := p)) ∣ p :=
  omega_exponent_of_derived_roots_aux hp (Nat.card G) rfl hG hroots
