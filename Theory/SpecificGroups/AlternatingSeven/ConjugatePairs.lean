module

public import Theory.Alternating.Aut
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The transposition forced by S₃ conjugate pairs in a faithful A₇ extension

A non-transposition involution on seven letters is a double or triple
transposition. Explicit even conjugators give products of order five or seven,
respectively. Cycle-type conjugacy transports these witnesses to every such
involution, preserving their membership in A₇. Neither product can belong to
a two-group or to S₃.

The actual conjugation equivalence Aut(A₇) ≃ S₇ then gives every faithful
normal A₇ extension with the S₃ pair condition a permutation marking extending
the supplied component coordinates. The transposition makes this marking onto.
No condition on the characteristic of a fixed group is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.5.21,
printed p.924 (PDF p.941); GLS3, Theorem 5.2.1 for Aut(A₇).
-/

@[expose] public section
open Equiv Equiv.Perm Subgroup
namespace AlternatingSeven.ConjugatePairs
abbrev S7 := Perm (Fin 7)
abbrev A7 := alternatingGroup (Fin 7)

private def doubleSwap : S7 := swap 0 1 * swap 2 3
private def tripleSwap : S7 := swap 0 1 * swap 2 3 * swap 4 5
private def doubleConjugator : S7 := swap 1 2 * swap 3 4
private def tripleConjugator : S7 := swap 1 2 * (swap 3 4 * swap 4 5 * swap 5 6)

private theorem double_type : doubleSwap.cycleType = {2,2} := by decide +kernel
private theorem triple_type : tripleSwap.cycleType = {2,2,2} := by decide +kernel
private theorem double_even : doubleConjugator ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel
private theorem triple_even : tripleConjugator ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel
private theorem double_order :
    orderOf (doubleSwap * (doubleConjugator * doubleSwap * doubleConjugator⁻¹)) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private theorem triple_order :
    orderOf (tripleSwap * (tripleConjugator * tripleSwap * tripleConjugator⁻¹)) = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem transport_pair {σ τ r : S7} {q : ℕ}
    (h : IsConj τ σ) (hr : r ∈ alternatingGroup (Fin 7))
    (ho : orderOf (τ * (r * τ * r⁻¹)) = q) :
    ∃ k : A7, orderOf (σ * ((k : S7) * σ * (k : S7)⁻¹)) = q := by
  obtain ⟨p,hp⟩ := isConj_iff.mp h
  refine ⟨⟨p * r * p⁻¹, (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem r hr p⟩, ?_⟩
  change orderOf (σ * ((p * r * p⁻¹) * σ * (p * r * p⁻¹)⁻¹)) = q
  rw [← hp]
  have he : (p * τ * p⁻¹) * ((p * r * p⁻¹) * (p * τ * p⁻¹) * (p * r * p⁻¹)⁻¹) =
      p * (τ * (r * τ * r⁻¹)) * p⁻¹ := by group
  rw [he, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ho]

/-- Actual even conjugators detect both non-transposition involution classes. -/
theorem nonswap_pair (σ : S7) (hσ : orderOf σ = 2) (hn : ¬ σ.IsSwap) :
    ∃ k : A7, orderOf (σ * ((k : S7) * σ * (k : S7)⁻¹)) = 5 ∨
      orderOf (σ * ((k : S7) * σ * (k : S7)⁻¹)) = 7 := by
  obtain ⟨k,hk⟩ := cycleType_prime_order (σ := σ) (hσ ▸ Nat.prime_two)
  rw [hσ] at hk
  have hb := σ.sum_cycleType_le
  rw [hk, Multiset.sum_replicate] at hb
  simp only [smul_eq_mul, Fintype.card_fin] at hb
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact (hn (isSwap_iff_cycleType.mpr (by simpa using hk))).elim
  · obtain ⟨r,hr⟩ := transport_pair
      (isConj_of_cycleType_eq (double_type.trans (by simpa using hk.symm))) double_even double_order
    exact ⟨r, Or.inl hr⟩
  · obtain ⟨r,hr⟩ := transport_pair
      (isConj_of_cycleType_eq (triple_type.trans (by simpa using hk.symm))) triple_even triple_order
    exact ⟨r, Or.inr hr⟩

/-- The conjugation isomorphism with the full automorphism group. -/
noncomputable def symmetricAutEquiv : S7 ≃* MulAut A7 :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

variable {E : Type*} [Group E] (K : Subgroup E) [K.Normal]
/-- The seven-point action induced by the original normal component. -/
noncomputable def action (e : K ≃* A7) : E →* S7 :=
  symmetricAutEquiv.symm.toMonoidHom.comp (normalConjThrough K e)

/-- The action retains the prescribed coordinates on the component. -/
theorem action_on_subgroup (e : K ≃* A7) (k : K) : action K e k = (e k : S7) := by
  apply symmetricAutEquiv.injective
  change symmetricAutEquiv (symmetricAutEquiv.symm _) = MulAut.conjNormal (e k).val
  rw [symmetricAutEquiv.apply_symm_apply, normalConjThrough_coe, MulAut.conjNormal_val]

/-- A trivial component centralizer makes the action faithful. -/
theorem action_injective (e : K ≃* A7) (hK : centralizer (K : Set E) = ⊥) :
    Function.Injective (action K e) :=
  symmetricAutEquiv.symm.injective.comp ((MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hK))

/-- The marking retains the original conjugation action. -/
theorem action_compatible (e : K ≃* A7) (g : E) (k : K) :
    (e (MulAut.conjNormal g k) : S7) = action K e g * (e k : S7) * (action K e g)⁻¹ := by
  rw [← action_on_subgroup, MulAut.conjNormal_apply, map_mul, map_mul, map_inv, action_on_subgroup]

private theorem pair_order_obstruction {v x : E} {q : ℕ}
    (hq : q.Prime) (h2 : q ≠ 2) (h6 : ¬ q ∣ 6)
    (ho : orderOf (v * (x * v * x⁻¹)) = q)
    (hp : ¬ IsPGroup 2 (zpowers v ⊔ (zpowers v).map (MulAut.conj x).toMonoidHom : Subgroup E) →
      Nonempty ((zpowers v ⊔ (zpowers v).map (MulAut.conj x).toMonoidHom : Subgroup E) ≃* Perm (Fin 3))) :
    False := by
  let B := zpowers v ⊔ (zpowers v).map (MulAut.conj x).toMonoidHom
  have hw : v * (x * v * x⁻¹) ∈ B := mul_mem
    ((le_sup_left : zpowers v ≤ B) (mem_zpowers v))
    ((le_sup_right : (zpowers v).map (MulAut.conj x).toMonoidHom ≤ B)
      (mem_map_of_mem _ (mem_zpowers v)))
  let w : B := ⟨_, hw⟩
  have how : orderOf w = q := (Subgroup.orderOf_coe w).symm.trans ho
  have hn : ¬ IsPGroup 2 B := by
    intro hb
    obtain ⟨n,hn⟩ := hb.exists_orderOf_dvd_pow w
    rw [how] at hn
    exact h2 ((Nat.dvd_prime Nat.prime_two).mp (hq.dvd_of_dvd_pow hn) |>.resolve_left hq.ne_one)
  obtain ⟨e⟩ := hp hn
  apply h6
  have hd := orderOf_dvd_natCard (e w)
  rw [e.orderOf_eq, how] at hd
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hd

/-- The exact S₃ pair condition for component conjugators forces a transposition. -/
theorem actor_isSwap (e : K ≃* A7) (hK : centralizer (K : Set E) = ⊥)
    (v : E) (hv : orderOf v = 2)
    (hp : ∀ x : K, ¬ IsPGroup 2
      (zpowers v ⊔ (zpowers v).map (MulAut.conj (x : E)).toMonoidHom : Subgroup E) →
      Nonempty ((zpowers v ⊔ (zpowers v).map (MulAut.conj (x : E)).toMonoidHom : Subgroup E) ≃* Perm (Fin 3))) :
    (action K e v).IsSwap := by
  by_contra hn
  have hf := action_injective K e hK
  have hσ : orderOf (action K e v) = 2 := (orderOf_injective _ hf v).trans hv
  obtain ⟨k,hk⟩ := nonswap_pair _ hσ hn
  let x := e.symm k
  have he : action K e (x : E) = (k : S7) := (action_on_subgroup K e x).trans
    (congrArg Subtype.val (e.apply_symm_apply k))
  have ho : orderOf (v * ((x : E) * v * (x : E)⁻¹)) =
      orderOf (action K e v * ((k : S7) * action K e v * (k : S7)⁻¹)) := by
    rw [← orderOf_injective (action K e) hf]
    simp only [map_mul, map_inv, he]
  rcases hk with hk | hk
  · exact pair_order_obstruction (by decide : Nat.Prime 5) (by decide) (by decide)
      (ho.trans hk) (hp x)
  · exact pair_order_obstruction (by decide : Nat.Prime 7) (by decide) (by decide)
      (ho.trans hk) (hp x)

/-- A₇ and the marked transposition fill the whole symmetric group. -/
theorem action_surjective_of_isSwap (e : K ≃* A7) (v : E)
    (hv : (action K e v).IsSwap) : Function.Surjective (action K e) := by
  have hout : action K e v ∉ alternatingGroup (Fin 7) := by
    rw [mem_alternatingGroup, hv.sign_eq]
    decide
  have heven (a : S7) (ha : a ∈ alternatingGroup (Fin 7)) :
      ∃ x : E, action K e x = a := by
    obtain ⟨x,hx⟩ := e.surjective ⟨a,ha⟩
    exact ⟨x, (action_on_subgroup K e x).trans (congrArg Subtype.val hx)⟩
  intro a
  by_cases ha : a ∈ alternatingGroup (Fin 7)
  · exact heven a ha
  · have hh : a * (action K e v)⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
      exact iff_of_false ha hout
    obtain ⟨x,hx⟩ := heven _ hh
    exact ⟨x * v, by rw [map_mul, hx, inv_mul_cancel_right]⟩

/-- Condition (iv) gives the whole faithful extension its compatible S₇ marking. -/
theorem exists_marked_equiv (e : K ≃* A7) (hK : centralizer (K : Set E) = ⊥)
    (v : E) (hv : orderOf v = 2)
    (hp : ∀ x : K, ¬ IsPGroup 2
      (zpowers v ⊔ (zpowers v).map (MulAut.conj (x : E)).toMonoidHom : Subgroup E) →
      Nonempty ((zpowers v ⊔ (zpowers v).map (MulAut.conj (x : E)).toMonoidHom : Subgroup E) ≃* Perm (Fin 3))) :
    ∃ q : E ≃* S7, (q v).IsSwap ∧ (∀ x : K, q x = (e x : S7)) ∧
      ∀ (g : E) (x : K), (e (MulAut.conjNormal g x) : S7) = q g * (e x : S7) * (q g)⁻¹ := by
  have hs := actor_isSwap K e hK v hv hp
  let q := MulEquiv.ofBijective (action K e)
    ⟨action_injective K e hK, action_surjective_of_isSwap K e v hs⟩
  exact ⟨q, hs, action_on_subgroup K e, action_compatible K e⟩
end AlternatingSeven.ConjugatePairs
