module
public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini
public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The last power map for an irreducible central omega

Let A be a finite abelian two-group whose first omega is nontrivial and
irreducible under a group of automorphisms. If A has exponent 2^m, the
last nonzero power map x ↦ x^(2^(m-1)) has invariant nontrivial image in
Ω₁(A), hence is onto it. Its kernel contains the squares. Since A/Φ(A)
and Ω₁(A) have the same order, this kernel is exactly Φ(A).

The resulting isomorphism A/Φ(A) ≃ Ω₁(A) commutes with every automorphism
of A. No exponent-two hypothesis or chosen homocyclic coordinates are
needed. The application identifies both natural sections of the whole
center in the nonbinary MS argument, at a single quotient marking.
Source context: Aschbacher–Smith C.1.34, printed pp.136–137; the proof is
the elementary power-map argument for an irreducible omega action.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.OmegaPowerBridge
variable {A H : Type*} [Group A] [Finite A] [IsMulCommutative A] [Group H]

/-- Irreducibility of the first omega identifies the last nonzero power map. -/
theorem exists_power_bridge (hA : IsPGroup 2 A) (hne : omega₁ A (p := 2) ≠ ⊥)
    (ρ : H →* MulAut A)
    (hirr : ∀ B : Subgroup A, B ≤ omega₁ A (p := 2) →
      (∀ g x, x ∈ B → ρ g x ∈ B) → B = ⊥ ∨ B = omega₁ A (p := 2)) :
    ∃ m : ℕ, 0 < m ∧ Monoid.exponent A = 2 ^ m ∧
      ∃ f : A →* omega₁ A (p := 2),
        (∀ x, (f x : A) = x ^ (2 ^ (m - 1))) ∧
        Function.Surjective f ∧ f.ker = frattini A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨m,hm⟩ := hA.exists_exponent_eq_pow
  have hmpos : 0 < m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    have hs : ∀ x : A, x = 1 := by
      intro x
      have hx := Monoid.pow_exponent_eq_one x
      simpa [hm,hm0] using hx
    apply hne
    exact bot_unique (fun x _ => mem_bot.mpr (hs x))
  have hmstep : m - 1 + 1 = m := by omega
  let f : A →* omega₁ A (p := 2) := {
    toFun x := ⟨x ^ (2 ^ (m - 1)), subset_closure (by
      change (x ^ (2 ^ (m - 1))) ^ (2 ^ 1) = 1
      rw [← pow_mul, ← pow_add, hmstep, ← hm]
      exact Monoid.pow_exponent_eq_one x)⟩
    map_one' := Subtype.ext (one_pow _)
    map_mul' x y := Subtype.ext (mul_pow x y _) }
  let B := (powMonoidHom (2 ^ (m-1)) : A →* A).range
  have hBO : B ≤ omega₁ A (p := 2) := by
    rintro x ⟨y,rfl⟩
    exact (f y).property
  have hBn : ∀ g x, x ∈ B → ρ g x ∈ B := by
    rintro g x ⟨y,rfl⟩
    exact ⟨ρ g y,(map_pow (ρ g) y _).symm⟩
  have hBne : B ≠ ⊥ := by
    intro hb
    have hp : ∀ x : A, x ^ (2^(m-1)) = 1 := by
      intro x
      exact mem_bot.mp (hb ▸ (show x ^ (2^(m-1)) ∈ B from ⟨x,rfl⟩))
    have hd := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp
    rw [hm] at hd
    have hle := Nat.le_of_dvd (pow_pos (by decide) _) hd
    have hlt := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) (show m-1<m by omega)
    omega
  have hBe : B = omega₁ A (p := 2) := (hirr B hBO hBn).resolve_left hBne
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := hBe.ge x.property
    exact ⟨y,Subtype.ext hy⟩
  have hphi : frattini A ≤ f.ker := by
    rw [← hA.square_range_eq_frattini]
    rintro x ⟨y,rfl⟩
    apply Subtype.ext
    change (y ^ 2) ^ (2 ^ (m-1)) = 1
    rw [← pow_mul, Nat.mul_comm 2, ← pow_succ, hmstep, ← hm]
    exact Monoid.pow_exponent_eq_one y
  have hidx : (frattini A).index = f.ker.index := by
    rw [index_eq_card, hA.card_frattini_quotient_eq_card_omega_one,
      index_ker, MonoidHom.range_eq_top.mpr hfs, card_top]
  have hcard : Nat.card (frattini A) = Nat.card f.ker := by
    have h1 := (frattini A).card_mul_index
    have h2 := f.ker.card_mul_index
    have hp : 0 < f.ker.index := Nat.card_pos (α := A ⧸ f.ker)
    rw [hidx] at h1
    nlinarith
  exact ⟨m,hmpos,hm,f,(fun _ => rfl),hfs,
    (eq_of_le_of_card_ge hphi hcard.ge).symm⟩

/-- The power bridge intertwines every automorphism of the original group. -/
theorem exists_equivariant_equiv (hA : IsPGroup 2 A) (hne : omega₁ A (p := 2) ≠ ⊥)
    (ρ : H →* MulAut A)
    (hirr : ∀ B : Subgroup A, B ≤ omega₁ A (p := 2) →
      (∀ g x, x ∈ B → ρ g x ∈ B) → B = ⊥ ∨ B = omega₁ A (p := 2)) :
    ∃ m : ℕ, 0 < m ∧ Monoid.exponent A = 2 ^ m ∧
      ∃ e : (A ⧸ frattini A) ≃* omega₁ A (p := 2),
        (∀ x, (e (QuotientGroup.mk' _ x) : A) = x ^ (2 ^ (m-1))) ∧
        ∀ (a : MulAut A) x,
          e (quotientAut (frattini A) a x) =
            OmegaAction.omegaRestriction A 2 1 a (e x) := by
  obtain ⟨m,hm,he,f,hf,hfs,hfk⟩ := exists_power_bridge hA hne ρ hirr
  let e : (A ⧸ frattini A) ≃* omega₁ A (p := 2) :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  have heq (x : A) : (e (QuotientGroup.mk' _ x) : A) = x ^ (2^(m-1)) := hf x
  refine ⟨m,hm,he,e,heq,?_⟩
  intro a x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini A) x
  apply Subtype.ext
  rw [quotientAut_apply_mk,heq]
  change (a x) ^ (2^(m-1)) = a (e (QuotientGroup.mk' _ x) : A)
  rw [heq,map_pow]
/-- If the original group is not elementary, every first-omega element has
an actual square root of order dividing four. -/
theorem square_roots_of_not_elementary (hA : IsPGroup 2 A)
    (hne : omega₁ A (p := 2) ≠ ⊥) (ρ : H →* MulAut A)
    (hirr : ∀ B : Subgroup A, B ≤ omega₁ A (p := 2) →
      (∀ g x, x ∈ B → ρ g x ∈ B) → B = ⊥ ∨ B = omega₁ A (p := 2))
    (hnot : ¬ ∀ x : A, x ^ 2 = 1) :
    ∀ x : omega₁ A (p := 2), ∃ y : omega A (p := 2) 2, (y : A)^2 = x := by
  obtain ⟨m,hm,hexp,f,hf,hs,_⟩ := exists_power_bridge hA hne ρ hirr
  have hm2 : 2 ≤ m := by
    by_contra hh
    have he : m = 1 := by omega
    apply hnot
    intro x
    have hx := Monoid.pow_exponent_eq_one x
    simpa only [hexp,he,pow_one] using hx
  intro x
  obtain ⟨z,hz⟩ := hs x
  have hz' : z ^ (2^(m-1)) = (x : A) := (hf z).symm.trans (congrArg Subtype.val hz)
  have hp : (z^(2^(m-2)))^2 = (x : A) := by
    rw [←pow_mul,←pow_succ,show m-2+1=m-1 by omega]
    exact hz'
  have hx : (x : A)^2=1 := by
    let : IsElementaryAbelian 2 (omega₁ A (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative A
    exact elemPow_eq_one_of_isElementaryAbelian _ x.property
  refine ⟨⟨z^(2^(m-2)),subset_closure ?_⟩,hp⟩
  change (z^(2^(m-2)))^4=1
  calc
    _ = ((z^(2^(m-2)))^2)^2 := pow_mul (z^(2^(m-2))) 2 2
    _ = 1 := by rw [hp,hx]
end Theory.GroupTheory.OmegaPowerBridge
