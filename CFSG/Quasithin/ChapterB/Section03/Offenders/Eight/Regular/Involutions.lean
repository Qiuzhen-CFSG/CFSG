module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Regular.Displacement

/-!
# Order-two fixed spaces inside regular elementary eight groups

A nonidentity element of an order-two subgroup acts without fixed points.
Choosing the smaller point in each pair identifies the eight points with
four representatives times a binary coordinate. Constant-displacement vectors
then have four freely chosen representative values and one common displacement.
Their coordinate sum is four times that displacement, hence zero. Quotienting
by the constant line gives fixed dimension four on the natural section.

This is the proper-subgroup calculation used for the regular groups in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Proposition
B.3.2(3),(6), printed pp.83–84.
-/

public section


open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders

/-- Choose one representative from each two-point orbit. -/
private theorem pair_coordinates (t : Equiv.Perm (Fin 8))
    (ht : Function.Involutive t) (hfree : ∀ i, t i ≠ i) :
    ∃ (R : Type) (_ : Fintype R) (e : R × Bool ≃ Fin 8),
      Fintype.card R = 4 ∧ ∀ r b, t (e (r, b)) = e (r, !b) := by
  let R := {i : Fin 8 // i < t i}
  let f : R × Bool → Fin 8 := fun p => if p.2 then t p.1.val else p.1.val
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, a⟩ ⟨s, b⟩ h
      cases a <;> cases b
      · have he : r = s := Subtype.ext h
        exact congrArg (fun x : R => (x, false)) he
      · have he : r.val = t s.val := h
        have hr := r.property
        have hs := s.property
        rw [he, ht] at hr
        exact False.elim (lt_asymm hr hs)
      · have he : t r.val = s.val := h
        have hr := r.property
        have hs := s.property
        rw [← he, ht] at hs
        exact False.elim (lt_asymm hr hs)
      · have he : r = s := Subtype.ext (t.injective h)
        exact congrArg (fun x : R => (x, true)) he
    · intro i
      by_cases hi : i < t i
      · exact ⟨(⟨i, hi⟩, false), rfl⟩
      · have hi' : t i < i := lt_of_le_of_ne (le_of_not_gt hi) (hfree i)
        refine ⟨(⟨t i, ?_⟩, true), ?_⟩
        · rw [ht]; exact hi'
        · exact ht i
  let e := Equiv.ofBijective f hf
  refine ⟨R, inferInstance, e, ?_, ?_⟩
  · have hc := Fintype.card_congr e
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at hc
    omega
  · intro r b
    cases b
    · rfl
    · exact ht r.val

private theorem order_two_generator {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 2) :
    ∃ t : B, (∀ b : B, b = 1 ∨ b = t) ∧
      Function.Involutive t.val ∧ ∀ i, t.val i ≠ i := by
  obtain ⟨t, ht, huniq⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  have hall (b : B) : b = 1 ∨ b = t := by
    by_cases h : b = 1
    · exact Or.inl h
    · exact Or.inr (huniq b h)
  have htt : t * t = 1 := by
    rcases hall (t * t) with h | h
    · exact h
    · have : t = 1 := mul_right_cancel (show t * t = 1 * t by simpa using h)
      exact (ht this).elim
  refine ⟨t, hall, ?_, ?_⟩
  · intro i
    have := congrArg (fun b : B => b.val i) htt
    exact this
  · intro i hi
    exact ht (regularEight_subgroup_free hA hBA t i hi)
/-- The pair coordinates give a linear parametrization by five binary scalars. -/
private theorem displacement_from_pairs (B : Subgroup (Equiv.Perm (Fin 8)))
    (t : B) (hall : ∀ b : B, b = 1 ∨ b = t)
    (R : Type) [Fintype R] (e : R × Bool ≃ Fin 8)
    (hcard : Fintype.card R = 4)
    (he : ∀ r b, t.val (e (r, b)) = e (r, !b)) :
    eightDisplacementSpace B ≤ core (Fin 8) ∧
      Module.finrank (ZMod 2) (eightDisplacementSpace B) = 5 := by
  classical
  let f₀ : ((R → ZMod 2) × ZMod 2) →ₗ[ZMod 2] Full (Fin 8) :=
    { toFun := fun p i => p.1 (e.symm i).1 + if (e.symm i).2 then p.2 else 0
      map_add' := by
        intro p q
        ext i
        dsimp
        split <;> ring
      map_smul' := by
        intro c p
        ext i
        dsimp
        split <;> simp [mul_add] }
  have hval (p : (R → ZMod 2) × ZMod 2) (r : R) (b : Bool) :
      f₀ p (e (r, b)) = p.1 r + if b then p.2 else 0 := by
    simp [f₀]
  have hmem (p : (R → ZMod 2) × ZMod 2) : f₀ p ∈ eightDisplacementSpace B := by
    rw [mem_eightDisplacementSpace_iff_forward]
    intro b
    rcases hall b with rfl | rfl
    · exact ⟨0, by intro i; simp⟩
    · refine ⟨p.2, ?_⟩
      intro i
      obtain ⟨⟨r, b⟩, rfl⟩ := e.surjective i
      rw [he, hval, hval]
      cases b <;> simp [ZModModule.neg_eq_self]
  let f := f₀.codRestrict (eightDisplacementSpace B) hmem
  have hinj : Function.Injective f := by
    intro p q hpq
    have hfun : f₀ p = f₀ q := congrArg Subtype.val hpq
    have hfirst : p.1 = q.1 := by
      funext r
      have := congrFun hfun (e (r, false))
      simpa only [hval, Bool.false_eq_true, if_false, add_zero] using this
    refine Prod.ext hfirst ?_
    obtain ⟨r⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card R by omega)
    have := congrFun hfun (e (r, true))
    simpa only [hval, if_true, hfirst, add_right_inj] using this
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨c, hc⟩ := (mem_eightDisplacementSpace_iff_forward B v.val).mp v.property t
    refine ⟨(fun r => v.val (e (r, false)), c), ?_⟩
    apply Subtype.ext
    ext i
    obtain ⟨⟨r, b⟩, rfl⟩ := e.surjective i
    change f₀ _ _ = _
    rw [hval]
    cases b
    · simp
    · have h := hc (e (r, false))
      rw [he] at h
      simp only [Bool.not_false] at h
      simp only [if_true]
      exact (add_comm _ _).trans (eq_add_of_sub_eq h).symm
  constructor
  · intro v hv
    obtain ⟨p, hp⟩ := hsurj ⟨v, hv⟩
    have hp' : f₀ p = v := congrArg Subtype.val hp
    rw [← hp', mem_core, ← Equiv.sum_comp e]
    rw [Fintype.sum_prod_type]
    simp_rw [hval]
    have hpair (r : R) :
        (∑ b : Bool, (p.1 r + if b then p.2 else 0)) = p.2 := by
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_zero]
      rw [add_right_comm, ZModModule.add_self, zero_add]
    simp_rw [hpair]
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    rw [show ((4 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
  · let ef := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
    rw [← ef.finrank_eq, Module.finrank_prod, Module.finrank_pi,
      Module.finrank_self, hcard]

private theorem regularEight_orderTwo_displacement_data
    {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 2) :
    eightDisplacementSpace B ≤ core (Fin 8) ∧
      Module.finrank (ZMod 2) (eightDisplacementSpace B) = 5 := by
  obtain ⟨t, hall, ht, hfree⟩ := order_two_generator hA hBA hB
  obtain ⟨R, inst, e, hcard, he⟩ := pair_coordinates t.val ht hfree
  let := inst
  exact displacement_from_pairs B t hall R e hcard he

/-- Constant-displacement vectors for an order-two subgroup of a regular eight
group all have even coordinate sum. -/
theorem regularEight_orderTwo_displacement_le_core
    {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 2) :
    eightDisplacementSpace B ≤ core (Fin 8) :=
  (regularEight_orderTwo_displacement_data hA hBA hB).1

/-- Four orbit values and one common displacement parametrize the preimage. -/
theorem regularEight_orderTwo_displacement_finrank
    {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 2) :
    Module.finrank (ZMod 2) (eightDisplacementSpace B) = 5 :=
  (regularEight_orderTwo_displacement_data hA hBA hB).2

/-- On the natural six-dimensional section an order-two subgroup of a regular
eight group has fixed dimension four. -/
theorem fixedSpace_natural_regularEight_orderTwo_finrank
    {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 2) :
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) B) = 4 := by
  have h := eightDisplacementSpace_finrank_eq_natural_add_one B
    (regularEight_orderTwo_displacement_le_core hA hBA hB)
  rw [regularEight_orderTwo_displacement_finrank hA hBA hB] at h
  omega

/-- The corresponding natural fixed codimension is two. -/
theorem fixedCodim_natural_regularEight_orderTwo
    {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 2) :
    fixedCodim (naturalRepresentation (Fin 8)) B = 2 := by
  apply fixedCodim_eq_of_finrank_fixedSpace _ B (d := 6) (k := 4)
  · simpa using finrank_natural_even (Fin 8) (by decide : Even 8)
  · exact fixedSpace_natural_regularEight_orderTwo_finrank hA hBA hB

end CFSG.Quasithin.ChapterB.Offenders
