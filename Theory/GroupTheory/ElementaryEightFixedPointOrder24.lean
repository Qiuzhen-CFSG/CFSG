module

public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.FinCases

/-!
# Order-twenty-four automorphisms fixing an elementary-eight element

An order-twenty-four subgroup of the automorphisms of an elementary abelian
2-group of order eight, fixing a specified nonidentity element, is isomorphic
to the symmetric group on four letters. This is the stabilizer recognition
used for the actual local normalizers in Stellmacher (9.1), journal p. 48.
No transitivity or splitting hypothesis is required.

Choose coordinates on the elementary group as a three-dimensional vector
space over `ZMod 2`. There are four characters to `C₂` taking the fixed
element to the nonidentity element, and these characters separate points.
The two finite coordinate facts are kernel-checked on `C₂ × C₂ × C₂`.
Inverse pullback gives a faithful action of the given automorphisms on those
four characters. Since both groups have order twenty-four, the action is an
isomorphism. All coordinate choices and character calculations are private.
-/

open scoped IsMulCommutative

private abbrev C := Multiplicative (ZMod 2)
private abbrev V := C × C × C
private def Good (z : V) (f : V → C) : Prop :=
  f 1 = 1 ∧ (∀ x y, f (x*y) = f x * f y) ∧ f z = Multiplicative.ofAdd 1
private instance (z : V) : DecidablePred (Good z) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private abbrev X (z : V) := {f : V → C // Good z f}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem countX : ∀ z : V, z ≠ 1 → Fintype.card (X z) = 4 := by
  intro z hz
  rw [Fintype.card_subtype]
  revert z
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1000 in
private theorem separates : ∀ z : V, z ≠ 1 → ∀ x y : V,
    (∀ f : X z, f.val x = f.val y) → x = y := by
  simp only [Subtype.forall]
  unfold Good
  decide +kernel

private noncomputable def coord (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hcard : Nat.card E = 8) : E ≃* V := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (2 : ℕ) ^ 3 = 8 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive E) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let basis := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hdim
  let first := AddEquiv.toMultiplicativeRight basis.equivFun.toAddEquiv
  exact first.trans {
    toFun := fun v => (Multiplicative.ofAdd (v.toAdd 0),
      Multiplicative.ofAdd (v.toAdd 1), Multiplicative.ofAdd (v.toAdd 2))
    invFun := fun v => Multiplicative.ofAdd ![v.1.toAdd, v.2.1.toAdd, v.2.2.toAdd]
    left_inv := by intro v; apply Multiplicative.toAdd.injective; funext i; fin_cases i <;> rfl
    right_inv := by intro v; rfl
    map_mul' := by intro v w; rfl }

private def pull {z : V} (a : MulAut V) (ha : a z = z) (f : X z) : X z :=
  ⟨f.val ∘ a, by
    refine ⟨?_, ?_, ?_⟩
    · simpa using f.property.1
    · intro x y
      simpa using f.property.2.1 (a x) (a y)
    · simpa [ha] using f.property.2.2⟩

private def rep {z : V} (A : Subgroup (MulAut V))
    (hfix : ∀ a : A, (a : MulAut V) z = z) : A →* Equiv.Perm (X z) where
  toFun a := {
    toFun := pull (a⁻¹ : A).val (hfix a⁻¹)
    invFun := pull a.val (hfix a)
    left_inv := by intro f; apply Subtype.ext; funext x; simp [pull]
    right_inv := by intro f; apply Subtype.ext; funext x; simp [pull] }
  map_one' := by ext f x; rfl
  map_mul' := by intro a b; ext f x; rfl

private theorem rep_injective {z : V} (hz : z ≠ 1) (A : Subgroup (MulAut V))
    (hfix : ∀ a : A, (a : MulAut V) z = z) : Function.Injective (rep A hfix) := by
  intro a b hab
  have hi : a⁻¹ = b⁻¹ := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    apply separates z hz
    intro f
    exact congrArg (fun p : Equiv.Perm (X z) => (p f).val x) hab
  exact inv_injective hi

/-- The order of an automorphism subgroup fixing a nonidentity point of
an elementary eight divides twenty-four. -/
public theorem elementaryEight_fixed_point_image_card_dvd_twentyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8) (z : E) (hz : z ≠ 1)
    (A : Subgroup (MulAut E))
    (hfix : ∀ a : A, (a : MulAut E) z = z) : Nat.card A ∣ 24 := by
  classical
  let (z : V) : Fintype (X z) := Subtype.fintype _
  let e := coord E hcard
  let conjugate : MulAut E ≃* MulAut V := MulAut.congr e
  let B := A.map conjugate.toMonoidHom
  let ab : A ≃* B := A.equivMapOfInjective conjugate.toMonoidHom conjugate.injective
  have hfixB : ∀ b : B, (b : MulAut V) (e z) = e z := by
    intro b
    obtain ⟨a, rfl⟩ := ab.surjective b
    change e ((a : MulAut E) (e.symm (e z))) = e z
    rw [e.symm_apply_apply, hfix a]
  have hzne : e z ≠ 1 := by
    intro he
    exact hz (e.injective (he.trans (e.map_one).symm))
  let r := (rep B hfixB).comp ab.toMonoidHom
  have hr : Function.Injective r := (rep_injective hzne B hfixB).comp ab.injective
  have hc : Nat.card (X (e z)) = 4 := by
    rw [Nat.card_eq_fintype_card]
    exact countX _ hzne
  have h := Subgroup.card_dvd_of_injective r hr
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (X (e z))),
    Fintype.card_perm, ← Nat.card_eq_fintype_card, hc] at h
  exact h

/-- An order-twenty-four automorphism subgroup fixing a nonidentity element
of an elementary group of order eight is `S₄`. -/
public theorem elementaryEight_fixed_point_order24_equiv_S4 {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8) (z : E) (hz : z ≠ 1)
    (A : Subgroup (MulAut E)) (hA : Nat.card A = 24)
    (hfix : ∀ a : A, (a : MulAut E) z = z) :
    Nonempty (A ≃* Equiv.Perm (Fin 4)) := by
  classical
  let (z : V) : Fintype (X z) := Subtype.fintype _
  let e := coord E hcard
  let conjugate : MulAut E ≃* MulAut V := MulAut.congr e
  let B := A.map conjugate.toMonoidHom
  let ab : A ≃* B := A.equivMapOfInjective conjugate.toMonoidHom conjugate.injective
  have hfixB : ∀ b : B, (b : MulAut V) (e z) = e z := by
    intro b
    obtain ⟨a, rfl⟩ := ab.surjective b
    change e ((a : MulAut E) (e.symm (e z))) = e z
    rw [e.symm_apply_apply, hfix a]
  have hzne : e z ≠ 1 := by
    intro he
    exact hz (e.injective (he.trans (e.map_one).symm))
  let r := (rep B hfixB).comp ab.toMonoidHom
  have hr : Function.Injective r := (rep_injective hzne B hfixB).comp ab.injective
  have hc : Nat.card (X (e z)) = 4 := by rw [Nat.card_eq_fintype_card]; exact countX _ hzne
  have hrCard : Nat.card A = Nat.card (Equiv.Perm (X (e z))) := by
    rw [hA, Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hc]
    decide
  exact ⟨(MulEquiv.ofBijective r ((Nat.bijective_iff_injective_and_card r).mpr ⟨hr, hrCard⟩)).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hc))⟩
