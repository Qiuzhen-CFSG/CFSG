module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum

/-!
# The three-part of two-local normalizer orders in A₉

A two-subgroup acting on nine points has orbits of sizes 1, 2, 4, and 8.
Its normalizer permutes orbits of equal size. If their respective numbers are
`a, b, c, d`, the kernel of this permutation action embeds in the product of
the symmetric groups on the individual orbits, while the image embeds in
`S_a × S_b × S_c × S_d`. Hence the normalizer order divides
`a! b! c! d! · (2!)^b (4!)^c (8!)^d`.

The equations `a + 2b + 4c + 8d = 9` and `a < 9` exclude divisibility by 27.
This includes the three two-point orbits case: permuting the three blocks
contributes only one factor of three. The argument works for any faithful
action on nine points, so no parity or normalizer classification is needed.

This supplies the normalizer-order premise of the A₉ QT calculation for
Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem 0.1.2(3),
printed p.4, repeated on p.482. It does not use QT as a hypothesis.
-/

namespace CFSG.Quasithin.MainConverse

open Equiv MulAction Subgroup
open scoped BigOperators

private def fiberPermHom {G α ι : Type*} [Group G]
    (ρ : G →* Perm α) (f : α → ι)
    (hf : ∀ g x, f (ρ g x) = f x) : G →* (∀ i, Perm {x // f x = i}) where
  toFun g i := (ρ g).subtypePerm (fun x => by rw [hf])
  map_one' := by ext i x; simp
  map_mul' g h := by
    ext i x
    exact Equiv.congr_fun (map_mul ρ g h) x.val

private theorem fiberPermHom_injective {G α ι : Type*} [Group G]
    (ρ : G →* Perm α) (hρ : Function.Injective ρ) (f : α → ι)
    (hf : ∀ g x, f (ρ g x) = f x) : Function.Injective (fiberPermHom ρ f hf) := by
  intro g h heq
  apply hρ
  ext x
  exact congrArg Subtype.val (Equiv.congr_fun (congrFun heq (f x)) ⟨x, rfl⟩)

private theorem card_dvd_fiber_factorials {G α ι : Type*} [Group G]
    [Finite α] [Fintype ι] (ρ : G →* Perm α) (hρ : Function.Injective ρ)
    (f : α → ι) (hf : ∀ g x, f (ρ g x) = f x) :
    Nat.card G ∣ ∏ i, (Nat.card {x // f x = i}).factorial := by
  classical
  have hd := card_dvd_of_injective (fiberPermHom ρ f hf)
    (fiberPermHom_injective ρ hρ f hf)
  simpa only [Nat.card_pi, Nat.card_perm] using hd

/-- Count the kernel on individual fibers and the image permuting equally labelled fibers. -/
private theorem card_dvd_two_level {G α ι κ : Type*} [Group G] [Finite G]
    [Finite α] [Fintype ι] [Fintype κ]
    (ρ : G →* Perm α) (hρ : Function.Injective ρ) (σ : G →* Perm ι)
    (f : α → ι) (c : ι → κ)
    (hf : ∀ g x, f (ρ g x) = σ g (f x))
    (hc : ∀ g i, c (σ g i) = c i) :
    Nat.card G ∣ (∏ i, (Nat.card {x // f x = i}).factorial) *
      ∏ j, (Nat.card {i // c i = j}).factorial := by
  have hk := card_dvd_fiber_factorials (ρ.comp σ.ker.subtype)
    (hρ.comp Subtype.val_injective) f (fun g x => by
      change f (ρ g.val x) = f x
      rw [hf, show σ g.val = 1 from g.property]
      rfl)
  have hr := card_dvd_fiber_factorials σ.range.subtype Subtype.val_injective c (by
    rintro ⟨_, g, rfl⟩ i
    exact hc g i)
  have heq : Nat.card G = Nat.card σ.ker * Nat.card σ.range := by
    rw [← σ.ker.card_mul_index, Subgroup.index_ker]
  rw [heq]
  exact Nat.mul_dvd_mul hk hr

private theorem normalizer_orbitRel {H α : Type*} [Group H] [MulAction H α]
    (Q : Subgroup H) (g : normalizer (Q : Set H)) {x y : α}
    (h : orbitRel Q α x y) : orbitRel Q α (g.val • x) (g.val • y) := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨⟨g.val * q.val * g.val⁻¹, ?_⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp g.property q.val).mp q.property
  · change (g.val * q.val * g.val⁻¹) • (g.val • y) = g.val • (q.val • y)
    simp only [smul_smul, inv_mul_cancel_right]

private def orbitPermHom {H α : Type*} [Group H] [MulAction H α]
    (Q : Subgroup H) : normalizer (Q : Set H) →* Perm (orbitRel.Quotient Q α) where
  toFun g :=
    { toFun := Quotient.map (fun x => g.val • x) (fun _ _ => normalizer_orbitRel Q g)
      invFun := Quotient.map (fun x => g.val⁻¹ • x) (fun _ _ => normalizer_orbitRel Q g⁻¹)
      left_inv := by intro x; induction x using Quotient.inductionOn; simp
      right_inv := by intro x; induction x using Quotient.inductionOn; simp }
  map_one' := by ext x; induction x using Quotient.inductionOn; simp
  map_mul' g h := by ext x; induction x using Quotient.inductionOn; simp [smul_smul]

private def fiberTransport {G α ι : Type*} [Group G]
    (ρ : G →* Perm α) (σ : G →* Perm ι) (f : α → ι)
    (hf : ∀ g x, f (ρ g x) = σ g (f x)) (g : G) (i : ι) :
    {x // f x = i} ≃ {x // f x = σ g i} where
  toFun x := ⟨ρ g x, by rw [hf, x.property]⟩
  invFun x := ⟨ρ g⁻¹ x, by rw [hf, x.property]; simp⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

/-- Every nontrivial partition of nine into powers of two has this factorial bound. -/
private theorem numeric_bound (a b c d : ℕ)
    (h : a + 2 * b + 4 * c + 8 * d = 9) (ha : a < 9) :
    ¬ 27 ∣ (1 ^ a * 2 ^ b * 24 ^ c * 40320 ^ d) *
      (a.factorial * b.factorial * c.factorial * d.factorial) := by
  have hd : d ≤ 1 := by omega
  have hc : c ≤ 2 := by omega
  have hb : b ≤ 4 := by omega
  have haeq : a = 9 - (2 * b + 4 * c + 8 * d) := by omega
  rw [haeq] at ha ⊢
  interval_cases d <;> interval_cases c <;> interval_cases b
  all_goals first | omega | norm_num [Nat.factorial]

private theorem color_count {ι : Type*} [Fintype ι] (c : ι → Fin 4) :
    (∑ i, 2 ^ (c i).val) =
      Nat.card {i // c i = 0} + 2 * Nat.card {i // c i = 1} +
      4 * Nat.card {i // c i = 2} + 8 * Nat.card {i // c i = 3} := by
  classical
  have h := Fintype.sum_fiberwise' c (fun j : Fin 4 => 2 ^ j.val)
  simpa [Fin.sum_univ_succ, ← Nat.card_eq_fintype_card, mul_comm, add_assoc] using h.symm

private theorem color_product {ι : Type*} [Fintype ι] (c : ι → Fin 4) :
    (∏ i, (2 ^ (c i).val).factorial) =
      1 ^ Nat.card {i // c i = 0} * 2 ^ Nat.card {i // c i = 1} *
      24 ^ Nat.card {i // c i = 2} * 40320 ^ Nat.card {i // c i = 3} := by
  classical
  have h := Fintype.prod_fiberwise' c (fun j : Fin 4 => (2 ^ j.val).factorial)
  simpa [Fin.prod_univ_succ, ← Nat.card_eq_fintype_card, Nat.factorial, mul_assoc] using h.symm

private theorem orbit_fiber_card {H α : Type*} [Group H] [MulAction H α]
    (Q : Subgroup H) (x : α) :
    Nat.card {y // (Quotient.mk'' y : orbitRel.Quotient Q α) = Quotient.mk'' x} =
      Nat.card (orbit Q x) := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun y => Quotient.eq'')

private theorem orbit_fiber_size {H : Type*} [Group H] [MulAction H (Fin 9)]
    (Q : Subgroup H) (hQ : IsPGroup 2 Q) (i : orbitRel.Quotient Q (Fin 9)) :
    ∃ k : Fin 4, Nat.card {x // (Quotient.mk'' x : orbitRel.Quotient Q (Fin 9)) = i} =
      2 ^ k.val := by
  induction i using Quotient.inductionOn with | h x =>
  obtain ⟨k, hk⟩ := hQ.card_orbit x
  rw [orbit_fiber_card]
  have hb : Nat.card (orbit Q x) ≤ 9 := by
    simpa using Nat.card_le_card_of_injective (fun y : orbit Q x => (y : Fin 9))
      Subtype.val_injective
  have hk4 : k < 4 := by
    by_contra h
    have h16 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ k)
    norm_num at h16
    omega
  exact ⟨⟨k, hk4⟩, hk⟩

/-- The counting argument uses only a faithful action on nine points. -/
private theorem faithful_nine_normalizer {H : Type*} [Group H] [Finite H]
    [MulAction H (Fin 9)] [FaithfulSMul H (Fin 9)]
    (Q : Subgroup H) (hQne : Q ≠ ⊥) (hQ : IsPGroup 2 Q) :
    ¬ 27 ∣ Nat.card (normalizer (Q : Set H)) := by
  classical
  let Ω := orbitRel.Quotient Q (Fin 9)
  let : Fintype Ω := Fintype.ofFinite Ω
  let f : Fin 9 → Ω := Quotient.mk''
  let N := normalizer (Q : Set H)
  let ρ : N →* Perm (Fin 9) := (MulAction.toPermHom H (Fin 9)).comp N.subtype
  have hρ : Function.Injective ρ := MulAction.toPerm_injective.comp Subtype.val_injective
  let σ : N →* Perm Ω := orbitPermHom Q
  have hf : ∀ g x, f (ρ g x) = σ g (f x) := fun _ _ => rfl
  choose c hsize using orbit_fiber_size Q hQ
  have hc : ∀ g i, c (σ g i) = c i := by
    intro g i
    apply Fin.ext
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ (c (σ g i)).val = 2 ^ (c i).val
    rw [← hsize, ← hsize]
    exact (Nat.card_congr (fiberTransport ρ σ f hf g i)).symm
  have hdvd := card_dvd_two_level ρ hρ σ f c hf hc
  have hsum : (∑ i, 2 ^ (c i).val) = 9 := by
    simp_rw [← hsize]
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f)]
    simp
  have hcount := (color_count c).symm.trans hsum
  have hzero : Nat.card {i // c i = 0} < 9 := by
    by_contra h
    have hz : Nat.card {i // c i = 0} = 9 := by omega
    have hpos : ∀ i, c i = 0 := by
      intro i
      by_contra hi
      have : Nonempty {j // c j = c i} := ⟨⟨i, rfl⟩⟩
      have hb : 0 < Nat.card {j // c j = c i} := Nat.card_pos
      have hci : c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
      rcases hci with he | he | he <;> rw [he] at hb <;> omega
    apply hQne
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 9)
    intro x
    have hs : Nat.card (orbit Q x) = 1 := by
      rw [← orbit_fiber_card Q x, hsize, hpos]
      rfl
    have hfix := (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by
      simpa only [Nat.card_eq_fintype_card] using hs))
    exact (mem_fixedPoints.mp hfix ⟨q, hq⟩).trans (one_smul H x).symm
  have hbound := numeric_bound _ _ _ _ hcount hzero
  intro h27
  apply hbound
  have hh := h27.trans hdvd
  change 27 ∣ (∏ i, (Nat.card {x // (Quotient.mk'' x : Ω) = i}).factorial) *
    ∏ j, (Nat.card {i // c i = j}).factorial at hh
  simp_rw [hsize] at hh
  rw [color_product] at hh
  simpa [Fin.prod_univ_succ, mul_assoc] using hh

/-- The normalizer of a nonidentity two-subgroup of A₉ has order not divisible by 27. -/
public theorem alternatingNine_normalizer_card_not_dvd_27
    (Q : Subgroup (alternatingGroup (Fin 9))) (hQne : Q ≠ ⊥) (hQ : IsPGroup 2 Q) :
    ¬ 27 ∣ Nat.card (normalizer (Q : Set (alternatingGroup (Fin 9)))) :=
  faithful_nine_normalizer Q hQne hQ

end CFSG.Quasithin.MainConverse
