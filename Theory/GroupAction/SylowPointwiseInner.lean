module

public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.AutomorphismOddOuter

/-!
# Pointwise Sylow stabilizers and perfect central quotients

Sylow conjugacy transports a pointwise stabilizer calculation from one Sylow
subgroup to every Sylow subgroup, retaining the conjugating element in that
subgroup. The same calculation lifts through the center of a perfect group:
the actual quotient action is faithful, and a conjugating element in the image
of a Sylow subgroup lifts to that Sylow subgroup.

An odd outer index also makes every automorphism of two-power order inner.
There is no reduction here from arbitrary two-elements to involutions.
These are the elementary transport steps used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.6, printed p.1172.
-/

public section

namespace MulAut
open Subgroup
open scoped Pointwise

variable {G H : Type*} [Group G] [Group H]

/-- Transport a pointwise-inner calculation between conjugate subgroups. -/
theorem fixing_inner_map (U : Subgroup G)
    (hU : ∀ a : MulAut G, (∀ x ∈ U, a x = x) → ∃ x ∈ U, a = conj x)
    (e a : MulAut G) (ha : ∀ x ∈ U.map e.toMonoidHom, a x = x) :
    ∃ x ∈ U.map e.toMonoidHom, a = conj x := by
  let b := e⁻¹ * a * e
  have hb : ∀ x ∈ U, b x = x := by
    intro x hx
    change e.symm (a (e x)) = x
    rw [ha (e x) (mem_map_of_mem e.toMonoidHom hx), e.symm_apply_apply]
  obtain ⟨x, hx, he⟩ := hU b hb
  refine ⟨e x, mem_map_of_mem e.toMonoidHom hx, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  have hz := congrArg (fun c : MulAut G => e (c z)) he
  change e (e.symm (a (e z))) = e (x * z * x⁻¹) at hz
  simpa only [e.apply_symm_apply, map_mul, map_inv, conj_apply] using hz

/-- A calculation for one Sylow subgroup supplies every conjugate Sylow. -/
theorem fixing_inner_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G)
    (hP : ∀ a : MulAut G, (∀ x ∈ P, a x = x) → ∃ x ∈ P, a = conj x)
    (a : MulAut G) (ha : ∀ x ∈ Q, a x = x) :
    ∃ x ∈ Q, a = conj x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hm : (P : Subgroup G).map (conj g).toMonoidHom = Q :=
    congrArg (fun R : Sylow p G => (R : Subgroup G)) hg
  change ∀ x ∈ (Q : Subgroup G), a x = x at ha
  change ∃ x ∈ (Q : Subgroup G), a = conj x
  simpa only [hm] using fixing_inner_map (P : Subgroup G) hP (conj g) a
    (by simpa only [hm] using ha)

/-- The quotient action has exactly the original automorphism order. -/
theorem orderOf_centralQuotientAction [Group.IsPerfect G]
    (e : G ⧸ center G ≃* H) (a : MulAut G) :
    orderOf (centralQuotientAction e a) = orderOf a :=
  orderOf_injective (centralQuotientAction e) (centralQuotientAction_injective e) a

/-- Lift pointwise Sylow innerness from an actual central quotient model.
The conjugating element remains in the specified Sylow subgroup upstairs. -/
theorem fixing_sylow_inner_of_centralQuotient [Finite G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (e : G ⧸ center G ≃* H)
    (hH : ∀ (Q : Sylow p H) (b : MulAut H),
      (∀ y ∈ Q, b y = y) → ∃ y ∈ Q, b = conj y)
    (P : Sylow p G) (a : MulAut G) (ha : ∀ x ∈ P, a x = x) :
    ∃ x ∈ P, a = conj x := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center G))
  let Q := P.mapSurjective (f := f) hf
  have hb : ∀ y ∈ Q, centralQuotientAction e a y = y := by
    rintro y ⟨x, hx, rfl⟩
    change centralQuotientAction e a (e (QuotientGroup.mk' (center G) x)) = _
    rw [centralQuotientAction_apply, ha x hx]
    rfl
  obtain ⟨y, hy, he⟩ := hH Q (centralQuotientAction e a) hb
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x, hx, centralQuotientAction_injective e ?_⟩
  rw [centralQuotientAction_conj]
  exact he

/-- Odd outer index excludes every nontrivial two-power image in the outer
quotient, including images of automorphisms of order greater than two. -/
theorem inner_of_two_pow_eq_one_of_odd_index [Finite G]
    (hodd : Odd (conj : G →* MulAut G).range.index)
    (a : MulAut G) {k : ℕ} (ha : a ^ (2 ^ k) = 1) :
    ∃ x : G, a = conj x := by
  let I := (conj : G →* MulAut G).range
  have hcard : Odd (Nat.card (MulAut G ⧸ I)) := hodd
  have hp : (QuotientGroup.mk' I a) ^ (2 ^ k) = 1 := by
    rw [← map_pow, ha, map_one]
  have he : QuotientGroup.mk' I a = 1 :=
    (hcard.coprime_two_right.pow_right k).pow_left_bijective.injective
      (by simpa using hp)
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff a).mp he
  exact ⟨x, hx.symm⟩

end MulAut
