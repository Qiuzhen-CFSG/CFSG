module

public import Theory.SpecificGroups.ReeTwo.CoreRootTwist
public import Theory.GroupTheory.CharacteristicTwoFrattiniFive
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction

/-!
# Marked normalization of the order-five action on the Ree core

Every order-five core automorphism is conjugate to the specified action `c`.
If it fixes root 2, the conjugator can fix both root 2 and its square, root 9.
No hypothesis on the cardinality of the fixed subgroup is required.

The last five roots belong to the Frattini subgroup, so the Frattini quotient
has at most 32 elements. Burnside's basis-kernel theorem embeds every
five-subgroup of the automorphism group into the automorphisms of this binary
space, whose order has five-part at most five. Sylow conjugacy, followed by
`a_conj_c`, then identifies every order-five automorphism with `c`.

An automorphism sends root 2 into the affine tail described in
`CoreRootConjugacy`. Its only points fixed by `c` are root 2 and its inverse.
The central automorphism `rootTwist` commutes with `c` and exchanges these two
points, so it repairs the marking after conjugacy.

Source: the core coordinates and complement action from Shinoda (1975),
(2.3), pp. 81–83, as verified in `Core`, `RootAction`, and `CoreRootTwist`;
the remaining argument is the standard Burnside basis and Sylow argument.
-/

open Subgroup
open scoped commutatorElement
namespace ReeTwo.Core

private theorem core_two : IsPGroup 2 Core := IsPGroup.of_card (n := 10) card

private theorem tail_mem_frattini (i : CoreRoot) (hi : 5 ≤ i.val) :
    root i ∈ frattini Core := by
  let _ : Fact (IsPGroup 2 Core) := ⟨core_two⟩
  have hc (x y : Core) : rightComm x y ∈ frattini Core := by
    apply commutator_le_frattini_of_isPGroup (p := 2)
    simpa [rightComm, commutatorElement_def, _root_.commutator_def] using
      (commutator_mem_commutator (show x⁻¹ ∈ (⊤ : Subgroup Core) from trivial)
        (show y⁻¹ ∈ (⊤ : Subgroup Core) from trivial))
  have h5 : rightComm (root 0) (root 2) = root 5 := by decide +kernel
  have h6 : rightComm (root 1) (root 2) = root 6 := by decide +kernel
  have h7 : rightComm (root 2) (root 3) = root 7 := by decide +kernel
  have h8 : rightComm (root 2) (root 4) = root 8 := by decide +kernel
  have h9 : root 2 ^ 2 = root 9 := by decide +kernel
  fin_cases i <;> norm_num at hi
  · exact h5 ▸ hc _ _
  · exact h6 ▸ hc _ _
  · exact h7 ▸ hc _ _
  · exact h8 ▸ hc _ _
  · exact h9 ▸ pth_power_mem_frattini_of_isPGroup (p := 2) _

/-- The first five binary root coordinates cover the Frattini quotient. -/
public theorem card_frattini_quotient_le_thirtytwo : Nat.card (Core ⧸ frattini Core) ≤ 32 := by
  let q := QuotientGroup.mk' (frattini Core)
  let f : (Fin 5 → ZMod 2) → Core ⧸ frattini Core := fun v =>
    q (root 0 ^ (v 0).val * root 1 ^ (v 1).val * root 2 ^ (v 2).val *
      root 3 ^ (v 3).val * root 4 ^ (v 4).val)
  have ht (i : CoreRoot) (hi : 5 ≤ i.val) : q (root i) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (tail_mem_frattini i hi)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (frattini Core) x
    refine ⟨![g.b0, g.b1, g.b2, g.b3, g.b4], ?_⟩
    change q (root 0 ^ g.b0.val * root 1 ^ g.b1.val * root 2 ^ g.b2.val *
      root 3 ^ g.b3.val * root 4 ^ g.b4.val) = q g
    have hn := congrArg q (normal_form g)
    simpa only [map_mul, map_pow, ht 5 (by decide), ht 6 (by decide),
      ht 7 (by decide), ht 8 (by decide), ht 9 (by decide), one_pow,
      _root_.mul_one] using hn
  have hn := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] using hn

private theorem five_subgroup_card_le (P : Subgroup (MulAut Core))
    (hP : IsPGroup 5 P) : Nat.card P ≤ 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (IsPGroup 2 Core) := ⟨core_two⟩
  let _ : IsElementaryAbelian 2 (Core ⧸ frattini Core) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) 2 := by
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_left n
  have hinj := MonoidHom.injective_frattini_action_of_coprime core_two P.subtype
    Subtype.val_injective hcop
  have hd := card_dvd_of_injective _ hinj
  have hnot := not_twentyfive_dvd_card_mulAut_of_elementary_two_card_le
    card_frattini_quotient_le_thirtytwo
  have hle : n ≤ 1 := by
    by_contra hh
    apply hnot
    exact (Nat.pow_dvd_pow 5 (by omega : 2 ≤ n)).trans (hn ▸ hd)
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hle

private def fiveSylow (rho : MulAut Core) (hrho : orderOf rho = 5) :
    Sylow 5 (MulAut Core) := by
  have hcard : Nat.card (zpowers rho) = 5 := (Nat.card_zpowers rho).trans hrho
  refine ⟨zpowers rho, IsPGroup.of_card (n := 1) hcard, ?_⟩
  intro Q hQ hle
  exact (eq_of_le_of_card_ge hle (hcard ▸ five_subgroup_card_le Q hQ)).symm

private theorem exists_conjugate_power (rho : MulAut Core) (hrho : orderOf rho = 5) :
    ∃ e : MulAut Core, ∃ k : ℕ, k < 5 ∧ e * rho * e⁻¹ = c ^ k := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq (MulAut Core)
    (fiveSylow rho hrho) (fiveSylow c orderOf_c)
  have hm : e * rho * e⁻¹ ∈ zpowers c := by
    have ht : rho ∈ fiveSylow rho hrho := by
      change rho ∈ zpowers rho
      exact mem_zpowers rho
    have hmem := Subgroup.smul_mem_pointwise_smul rho (MulAut.conj e)
      (fiveSylow rho hrho : Subgroup (MulAut Core)) ht
    change e * rho * e⁻¹ ∈ e • fiveSylow rho hrho at hmem
    rw [he] at hmem
    change e * rho * e⁻¹ ∈ zpowers c at hmem
    exact hmem
  have hm' := (isOfFinOrder_of_finite c).mem_zpowers_iff_mem_range_orderOf.mp hm
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm'
  refine ⟨e, k, ?_, heq.symm⟩
  simpa only [Finset.mem_range, orderOf_c] using hk

/-- All order-five core automorphisms are conjugate to the specified action. -/
public theorem exists_conjugator_c_of_orderOf_eq_five (rho : MulAut Core) (hrho : orderOf rho = 5) :
    ∃ e : MulAut Core, e * rho * e⁻¹ = c := by
  obtain ⟨e, k, hk, he⟩ := exists_conjugate_power rho hrho
  have hk0 : k ≠ 0 := by
    intro h
    have he1 : e * rho * e⁻¹ = 1 := by simpa only [h, pow_zero] using he
    have hr1 : rho = 1 := (MulAut.conj e).injective (he1.trans (map_one _).symm)
    rw [hr1, orderOf_one] at hrho
    norm_num at hrho
  have hc2 : IsConj c (c ^ 2) := isConj_iff.mpr ⟨a, a_conj_c⟩
  have hc4 : IsConj c (c ^ 4) := by
    have h := hc2.pow 2
    rw [← pow_mul] at h
    exact hc2.trans h
  have hc3 : IsConj c (c ^ 3) := by
    have h := hc4.pow 2
    rw [← pow_mul, show 4 * 2 = 5 + 3 from rfl, pow_add, c_five,
      _root_.one_mul] at h
    exact hc2.trans h
  have hp : IsConj (c ^ k) c := by
    interval_cases k
    · exact (hk0 rfl).elim
    · simpa using IsConj.refl c
    · exact hc2.symm
    · exact hc3.symm
    · exact hc4.symm
  exact isConj_iff.mp ((isConj_iff.mpr ⟨e, he⟩).trans hp)

set_option maxHeartbeats 8000000 in
private theorem fixed_affine_root : ∀ t u v w z : ZMod 2,
    c ⟨0, 0, 1, 0, 0, t, u, v, w, z⟩ = ⟨0, 0, 1, 0, 0, t, u, v, w, z⟩ →
    (⟨0, 0, 1, 0, 0, t, u, v, w, z⟩ : Core) = root 2 ∨
    (⟨0, 0, 1, 0, 0, t, u, v, w, z⟩ : Core) = (root 2)⁻¹ := by
  decide +kernel

private theorem fixed_aut_root_two (e : MulAut Core)
    (h : c (e (root 2)) = e (root 2)) :
    e (root 2) = root 2 ∨ e (root 2) = (root 2)⁻¹ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := aut_root_two_head e
  have he : e (root 2) = ⟨0, 0, 1, 0, 0, (e (root 2)).b5,
      (e (root 2)).b6, (e (root 2)).b7, (e (root 2)).b8, (e (root 2)).b9⟩ := by
    apply Core.ext <;> first | assumption | rfl
  rw [he] at h ⊢
  exact fixed_affine_root _ _ _ _ _ h

-- Abstract group operations here keep the kernel from unfolding the concrete action.
private theorem conjugator_fixed {G : Type*} [Group G]
    (rho sigma e : MulAut G) (x : G)
    (he : e * rho * e⁻¹ = sigma) (hx : rho x = x) : sigma (e x) = e x := by
  have heq : e * rho = sigma * e := by rw [← he]; group
  have hh := congrArg (fun f : MulAut G => f x) heq
  simp only [MulAut.mul_apply, hx] at hh
  exact hh.symm

private theorem twist_conjugator {G : Type*} [Group G]
    (rho sigma e t : MulAut G) (he : e * rho * e⁻¹ = sigma)
    (ht : Commute t sigma) : (t * e) * rho * (t * e)⁻¹ = sigma := by
  calc
    (t * e) * rho * (t * e)⁻¹ = t * (e * rho * e⁻¹) * t⁻¹ := by group
    _ = t * sigma * t⁻¹ := by rw [he]
    _ = sigma := by rw [ht.eq, mul_inv_cancel_right]

private theorem twist_root {G : Type*} [Group G]
    (e t : MulAut G) (x : G) (he : e x = x⁻¹) (ht : t x = x⁻¹) :
    (t * e) x = x := by
  rw [MulAut.mul_apply, he, map_inv, ht, inv_inv]

private theorem fixes_root_nine (d : MulAut Core) (hd : d (root 2) = root 2) :
    d (root 9) = root 9 := by
  have hs : root 2 ^ 2 = root 9 := by decide +kernel
  rw [← hs, map_pow, hd]

/-- Normalize the five-action while fixing the middle root and its central square. -/
public theorem exists_marked_conjugator_of_orderOf_eq_five
    (rho : MulAut Core) (hrho : orderOf rho = 5) (hroot : rho (root 2) = root 2) :
    ∃ d : MulAut Core, d (root 2) = root 2 ∧ d (root 9) = root 9 ∧
      d * rho * d⁻¹ = c := by
  obtain ⟨e, he⟩ := exists_conjugator_c_of_orderOf_eq_five rho hrho
  have hf := conjugator_fixed rho c e (root 2) he hroot
  rcases fixed_aut_root_two e hf with hpos | hneg
  · exact ⟨e, hpos, fixes_root_nine e hpos, he⟩
  · have hd := twist_root e rootTwist (root 2) hneg rootTwist_root_two
    exact ⟨rootTwist * e, hd, fixes_root_nine _ hd,
      twist_conjugator rho c e rootTwist he rootTwist_commute_c⟩

end ReeTwo.Core
