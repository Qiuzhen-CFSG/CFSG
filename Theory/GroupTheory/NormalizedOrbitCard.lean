module

public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# Strict conjugacy-orbit bounds in a normalized subgroup

A nonidentity element has its entire conjugacy orbit in the normalized
subgroup W, and that orbit omits the identity. Orbit-stabilizer gives the
strict inequality |A| < |W| |C_A(y)|. In particular, a large actor with
uniformly small stabilizers of moved elements must centralize W.

The consumer is the proper-flag-space step in Aschbacher--Smith 12.9.9(1),
printed p.863 of `refs/quasithin.pdf`; no linear-model assumptions are needed.
-/

public section

open Subgroup
namespace Subgroup

/-- The orbit of a nonidentity element in a normalized finite subgroup omits one. -/
theorem card_lt_normalized_card_mul_centralizer
    {G : Type*} [Group G] [Finite G] (A W : Subgroup G)
    (hAW : A ≤ normalizer (W : Set G)) (y : G) (hy : y ∈ W) (hy1 : y ≠ 1) :
    Nat.card A < Nat.card W * Nat.card (A ⊓ centralizer ({y} : Set G) : Subgroup G) := by
  let _ : MulAction A G := {
    smul := fun a x => (a : G) * x * (a : G)⁻¹
    one_smul := by intro x; change (1 : G) * x * (1 : G)⁻¹ = x; simp
    mul_smul := by
      intro a b x
      change ((a : G) * (b : G)) * x * ((a : G) * (b : G))⁻¹ =
        (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
      simp [mul_assoc] }
  have hstab : MulAction.stabilizer A y =
      (A ⊓ centralizer ({y} : Set G)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff]
    change (a : G) * y * (a : G)⁻¹ = y ↔ (a : G) ∈ A ∧ _
    rw [mul_inv_eq_iff_eq_mul]
    simp only [a.property, true_and]
    exact mem_centralizer_singleton_iff.symm
  let f : MulAction.orbit A y → W := fun x => ⟨x, by
    obtain ⟨a,ha⟩ := x.property
    change (a : G) * y * (a : G)⁻¹ = (x : G) at ha
    rw [← ha]
    exact (mem_normalizer_iff.mp (hAW a.property) y).mp hy⟩
  have hinj : Function.Injective f := by
    intro x z he
    apply Subtype.ext
    exact congrArg (fun w : W => (w : G)) he
  have hmiss : (1 : W) ∉ Set.range f := by
    rintro ⟨x,hx⟩
    have he : (x : G) = 1 := congrArg Subtype.val hx
    obtain ⟨a,ha⟩ := x.property
    change (a : G) * y * (a : G)⁻¹ = (x : G) at ha
    rw [he] at ha
    have hh : MulAut.conj (a : G) y = MulAut.conj (a : G) 1 := by simpa using ha
    exact hy1 ((MulAut.conj (a : G)).injective hh)
  have hlt : Nat.card (MulAction.orbit A y) < Nat.card W := by
    let := Fintype.ofFinite (MulAction.orbit A y)
    let := Fintype.ofFinite W
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_of_notMem f hinj hmiss
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A y)
  rw [Nat.card_prod, hstab,
    Nat.card_congr (subgroupOfEquivOfLe
      (show A ⊓ centralizer ({y} : Set G) ≤ A from inf_le_left)).toEquiv] at hc
  rw [← hc]
  exact Nat.mul_lt_mul_of_pos_right hlt Nat.card_pos

/-- Small stabilizers of moved elements force a sufficiently large actor to fix W. -/
theorem centralizes_of_small_point_stabilizers
    {G : Type*} [Group G] [Finite G] (A W : Subgroup G)
    (hAW : A ≤ normalizer (W : Set G)) (k : ℕ)
    (hsize : Nat.card W * k ≤ Nat.card A)
    (hsmall : ∀ y ∈ W, y ∉ centralizer (A : Set G) →
      Nat.card (A ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ k) :
    W ≤ centralizer (A : Set G) := by
  intro y hy
  by_contra hn
  have hy1 : y ≠ 1 := fun he => hn (he ▸ one_mem _)
  have hlt := card_lt_normalized_card_mul_centralizer A W hAW y hy hy1
  have hle := Nat.mul_le_mul_left (Nat.card W) (hsmall y hy hn)
  exact (Nat.not_lt_of_ge hsize) (hlt.trans_le hle)


end Subgroup
