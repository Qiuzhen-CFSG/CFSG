module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary

/-!
# Odd cardinality of the distinguished involutions in the distinguished subgroup

For a fixed `z ∈ Z ∩ M`, conjugation of `z` gives a permutation of `Z ∖ M`.
Injectivity follows from the odd-product lemma: if `s` and `t` have the same
image, `s * t` centralizes `z`, while the odd-order element `z * t` inverts
`s * t`. Thus `s * t` has square one as well as odd order, and `s = t`.
Restricting this permutation constructs a bijection from `Z ∩ Mt` to `Z ∩ M`
for every `t ∈ Z ∖ M`. Conjugation by `t` pairs the elements of `Z ∩ Mt`, with
`t` its unique fixed point, proving that both sets have odd cardinality.

This proves the parity assertion of GLS, Volume 4, Chapter 2, Proposition
3.6(e), printed p.30, using the coset-counting argument of Lemma 3.4(a–b),
pp.28–29. It avoids the intervening Z* argument and requires neither
minimality nor a rank hypothesis. The right coset `Mt` is represented by
`s * t ∈ M`, since `t` is an involution. In Lemma 3.4(a) the original source
has `x^z = x`; the transcription's `x^s = x` is erroneous.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem odd_inverter {c x : G} (hc : Odd (orderOf c))
    (hi : MulAut.conj c x = x⁻¹) : x = x⁻¹ := by
  have hs : Commute (c ^ 2) x := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      c ^ 2 * x * (c ^ 2)⁻¹ = MulAut.conj c (MulAut.conj c x) := by
        simp only [MulAut.conj_apply, pow_two]; group
      _ = x := by rw [hi, map_inv, hi, inv_inv]
  obtain ⟨k, hk⟩ := hc
  have he : c ^ (2 * k) * c = 1 := by
    rw [← pow_succ, ← hk, pow_orderOf_eq_one]
  have hcomm : Commute (c ^ (2 * k)) x := by
    simpa only [pow_mul] using hs.pow_left k
  have hcx : Commute c x := by
    have hcinv : c = (c ^ (2 * k))⁻¹ := by
      have hh := congrArg Inv.inv (eq_inv_iff_mul_eq_one.mpr he)
      simpa using hh.symm
    rw [hcinv]
    exact hcomm.inv_left
  exact (mul_inv_eq_iff_eq_mul.mpr hcx.eq).symm.trans hi

omit [Finite G] in
private theorem odd_square_one {x : G} (ho : Odd (orderOf x)) (hx : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := ho
  have hp := pow_orderOf_eq_one x
  rw [hk, pow_succ, pow_mul, hx, one_pow, one_mul] at hp
  exact hp

private theorem outside_injective (h : IsProductDisconnected Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {s t : G} (hs : s ∈ Z) (_hsM : s ∉ M) (ht : t ∈ Z) (htM : t ∉ M)
    (he : MulAut.conj (s : G) z = MulAut.conj t z) : s = t := by
  have si := (h.involutions s hs).inv_eq_self
  have ti := (h.involutions t ht).inv_eq_self
  have ss : s * s = 1 := by simpa [pow_two] using (h.involutions s hs).sq_eq_one
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  have hc : Commute (s * t) z := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (s * t) * z * (s * t)⁻¹ = MulAut.conj s (MulAut.conj t z) := by
        simp only [MulAut.conj_apply]; group
      _ = MulAut.conj s (MulAut.conj (s : G) z) := by rw [he]
      _ = z := by
        simp only [MulAut.conj_apply, si]
        calc
          s * (s * z * s) * s = (s * s) * z * (s * s) := by group
          _ = z := by simp [ss]
  have hxM : s * t ∈ M := h.centralizer_le hz hzM
    (Subgroup.mem_centralizer_singleton_iff.mpr hc.eq)
  have hxodd := productDisconnected_odd_orderOf_mul h hs ht htM (Or.inr hxM)
  have hct : MulAut.conj t (s * t) = (s * t)⁻¹ := by
    simp [MulAut.conj_apply, mul_inv_rev, si, ti, mul_assoc, tt]
  have hcz : MulAut.conj z (s * t) = s * t :=
    mul_inv_eq_iff_eq_mul.mpr hc.symm.eq
  have hcx : MulAut.conj (z * t) (s * t) = (s * t)⁻¹ := by
    calc
      _ = MulAut.conj z (MulAut.conj t (s * t)) := by
        simp only [MulAut.conj_apply]; group
      _ = (s * t)⁻¹ := by rw [hct, map_inv, hcz]
  have hinv := odd_inverter
    (productDisconnected_odd_orderOf_mul h hz ht htM (Or.inl hzM)) hcx
  have hone : s * t = 1 := odd_square_one hxodd (by
    rw [pow_two]
    nth_rw 1 [hinv]
    exact inv_mul_cancel _)
  exact (eq_inv_iff_mul_eq_one.mpr hone).trans ti

/-- GLS Lemma 3.4(b), for a right coset represented by a distinguished
involution outside `M`. This is the instance needed for the parity argument. -/
public theorem productDisconnected_card_right_coset (h : IsProductDisconnected Z M)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M) :
    Nat.card {s : G // s ∈ Z ∧ s * t ∈ M} =
      Nat.card {z : G // z ∈ Z ∧ z ∈ M} := by
  classical
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  let O := {s : G // s ∈ Z ∧ s ∉ M}
  let f : O → O := fun s => ⟨MulAut.conj (s : G) z, h.invariant s z hz,
    fun hm => s.property.2 ((h.conjugate_mem_iff z hz hzM s).mp hm)⟩
  have hf : Function.Injective f := by
    intro s u he
    exact Subtype.ext (outside_injective h hz hzM s.property.1 s.property.2
      u.property.1 u.property.2 (congrArg Subtype.val he))
  have hsur := Finite.surjective_of_injective hf
  have ti := (h.involutions t ht).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  have hcomp (s : G) : MulAut.conj t (MulAut.conj (s : G) z) = MulAut.conj (t * s) z := by
    simp only [MulAut.conj_apply]; group
  have hout {s : G} (hm : s * t ∈ M) : s ∉ M := by
    intro hs
    apply htM
    have hh := M.mul_mem (M.inv_mem hs) hm
    simpa only [inv_mul_cancel_left] using hh
  have hrev {s : G} (hs : s ∈ Z) : (s * t)⁻¹ = t * s := by
    rw [mul_inv_rev, ti, (h.involutions s hs).inv_eq_self]
  let g : {s : G // s ∈ Z ∧ s * t ∈ M} → {a : G // a ∈ Z ∧ a ∈ M} :=
    fun s => ⟨MulAut.conj t (MulAut.conj (s : G) z), h.invariant _ _ (h.invariant _ _ hz), by
      rw [hcomp]
      apply (h.conjugate_mem_iff z hz hzM _).mpr
      rw [← hrev s.property.1]
      exact M.inv_mem s.property.2⟩
  apply Nat.card_congr (Equiv.ofBijective g ⟨?_, ?_⟩)
  · intro s u he
    have he' := (MulAut.conj t).injective (congrArg Subtype.val he)
    exact Subtype.ext (outside_injective h hz hzM s.property.1 (hout s.property.2)
      u.property.1 (hout u.property.2) he')
  · intro a
    let b : O := ⟨MulAut.conj t a, h.invariant _ _ a.property.1,
      fun hm => htM ((h.conjugate_mem_iff a a.property.1 a.property.2 t).mp hm)⟩
    obtain ⟨s, hs⟩ := hsur b
    have he : MulAut.conj (s : G) z = MulAut.conj t a := congrArg Subtype.val hs
    have he' : MulAut.conj t (MulAut.conj (s : G) z) = a := by
      rw [he]
      simp only [MulAut.conj_apply, ti]
      calc
        t * (t * (a : G) * t) * t = (t * t) * (a : G) * (t * t) := by group
        _ = a := by simp [tt]
    have hm : t * (s : G) ∈ M :=
      (h.conjugate_mem_iff z hz hzM _).mp (by rw [← hcomp, he']; exact a.property.2)
    have hsm : (s : G) * t ∈ M := by
      have hh := M.inv_mem hm
      simpa only [mul_inv_rev, ti, (h.involutions s s.property.1).inv_eq_self] using hh
    exact ⟨⟨s, s.property.1, hsm⟩, Subtype.ext he'⟩

/-- The involutions in an outside coset have odd cardinality: conjugation
by its representative `t` pairs all of them except `t` itself. -/
private theorem odd_card_coset (h : IsProductDisconnected Z M)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M) :
    Odd (Nat.card {s : G // s ∈ Z ∧ s * t ∈ M}) := by
  classical
  let T := {s : G // s ∈ Z ∧ s * t ∈ M}
  let : Fintype T := Fintype.ofFinite T
  have ti := (h.involutions t ht).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  let f : T → T := fun s => ⟨MulAut.conj t s, h.invariant _ _ s.property.1, by
    have hi := M.inv_mem s.property.2
    have si := (h.involutions s s.property.1).inv_eq_self
    have he : MulAut.conj t (s : G) * t = ((s : G) * t)⁻¹ := by
      simp [MulAut.conj_apply, mul_inv_rev, ti, si, mul_assoc, tt]
    rw [he]
    exact hi⟩
  have hf : Function.Involutive f := by
    intro s
    apply Subtype.ext
    change t * (t * (s : G) * t⁻¹) * t⁻¹ = s
    rw [ti]
    calc
      t * (t * (s : G) * t) * t = (t * t) * (s : G) * (t * t) := by group
      _ = s := by simp [tt]
  let e : Equiv.Perm T := ⟨f, f, hf, hf⟩
  let a : T := ⟨t, ht, by simp [tt]⟩
  have ha : e a = a := by
    apply Subtype.ext
    change t * t * t⁻¹ = t
    simp [mul_assoc]
  have hu : ∀ s : T, e s = s → s = a := by
    intro s hs
    have hc : Commute t (s : G) := mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hs)
    have hsq : ((s : G) * t) ^ 2 = 1 := by
      rw [hc.symm.mul_pow, (h.involutions s s.property.1).sq_eq_one,
        (h.involutions t ht).sq_eq_one, one_mul]
    have he := odd_square_one
      (productDisconnected_odd_orderOf_mul h s.property.1 ht htM (Or.inr s.property.2)) hsq
    apply Subtype.ext
    exact (eq_inv_iff_mul_eq_one.mpr he).trans ti
  have hp : e ^ (2 ^ 1) = 1 := by
    apply Equiv.ext
    intro s
    change f (f s) = s
    exact hf s
  by_contra hn
  have hd : 2 ∣ Fintype.card T := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.not_odd_iff_even.mp hn).two_dvd
  obtain ⟨s, hs, hne⟩ := Equiv.Perm.exists_fixed_point_of_prime' hd hp ha
  exact hne (hu s hs)

/-- The parity assertion of GLS, Volume 4, Chapter 2, Proposition 3.6(e).
Only product disconnection is needed, without a minimal-counterexample or
rank hypothesis. -/
public theorem productDisconnected_odd_card (h : IsProductDisconnected Z M) :
    Odd (Nat.card {z : G // z ∈ Z ∧ z ∈ M}) := by
  obtain ⟨t, ht, htM⟩ := exists_not_mem h
  rw [← productDisconnected_card_right_coset h ht htM]
  exact odd_card_coset h ht htM

end BenderSuzuki.ZD
