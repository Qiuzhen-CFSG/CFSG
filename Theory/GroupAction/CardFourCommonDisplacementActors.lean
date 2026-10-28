module
public import Theory.GroupAction.Lemmas
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Mathlib.GroupTheory.Index

/-!
# Comparing two actors with displacement of order four

Two automorphisms of a finite abelian group have displacement groups of order
four, with a common nontrivial subgroup S and a common line L. Suppose S lies
in U, the order of U is the square of the order of S, and U is disjoint from C.
If their difference actor has displacement in C but not of order two, then
the actors agree or U has order four and contains L.

Distinct displacement planes intersect in a line, forcing S=L and order U=4.
If the planes coincide, the difference displacement lies in that plane and C.
This intersection is proper because it misses nontrivial S, so it has order
at most two. The excluded order-two case makes the difference action trivial.
The proof keeps all action groups and distinguished subgroups explicit.

This finite subgroup/action calculation isolates the two alternatives used
in Stellmacher (10.1), printed p.63, before source assertion (13).
-/

private theorem displacement_le_of_pointwise
    {W : Type*} [CommGroup W] (actor : MulAut W) (D : Subgroup W)
    (h : ∀ w : W, w⁻¹ * actor w ∈ D) :
    commutatorAction (Subgroup.zpowers actor) W ≤ D := by
  let K : Subgroup (MulAut W) := {
    carrier := {a | ∀ w : W, w⁻¹ * a w ∈ D}
    one_mem' := by intro w; simp
    mul_mem' := by
      intro a b ha hb w
      have hh := D.mul_mem (hb w) (ha (b w))
      change w⁻¹ * a (b w) ∈ D
      simpa only [mul_assoc, mul_inv_cancel_left] using hh
    inv_mem' := by
      intro a ha w
      have hh := D.inv_mem (ha (a⁻¹ w))
      simpa only [MulAut.apply_inv_self, mul_inv_rev, inv_inv] using hh }
  have hk : Subgroup.zpowers actor ≤ K := Subgroup.zpowers_le.mpr h
  rw [commutatorAction_eq_closure, Subgroup.closure_le]
  rintro point ⟨a, w, rfl⟩
  exact hk a.property w

private theorem proper_subgroup_card_le_two_of_card_four
    {W : Type*} [Group W] [Finite W] (D J : Subgroup W)
    (hD : Nat.card D = 4) (hJD : J ≤ D) (hne : J ≠ D) :
    Nat.card J ≤ 2 := by
  have hle : Nat.card J ≤ 4 := (Subgroup.card_le_of_le hJD).trans hD.le
  have hfour : Nat.card J ≠ 4 := fun hh => hne
    (Subgroup.eq_of_le_of_card_ge hJD (by rw [hD, hh]))
  have hdvd : Nat.card J ∣ 4 := hD ▸ Subgroup.card_dvd_of_le hJD
  have hthree : Nat.card J ≠ 3 := by intro hh; norm_num [hh] at hdvd
  omega

public theorem eq_or_card_four_support_of_common_displacement
    {W : Type*} [CommGroup W] [Finite W]
    (first second : MulAut W) (U C S L : Subgroup W)
    (hfirst : Nat.card (commutatorAction (Subgroup.zpowers first) W) = 4)
    (hsecond : Nat.card (commutatorAction (Subgroup.zpowers second) W) = 4)
    (hS : S ≠ ⊥) (hSU : S ≤ U)
    (hSfirst : S ≤ commutatorAction (Subgroup.zpowers first) W)
    (hSsecond : S ≤ commutatorAction (Subgroup.zpowers second) W)
    (hL : Nat.card L = 2)
    (hLfirst : L ≤ commutatorAction (Subgroup.zpowers first) W)
    (hLsecond : L ≤ commutatorAction (Subgroup.zpowers second) W)
    (hU : Nat.card U = Nat.card S ^ 2) (hUC : Disjoint U C)
    (hdelta : commutatorAction (Subgroup.zpowers (first⁻¹ * second)) W ≤ C)
    (hno : Nat.card (commutatorAction (Subgroup.zpowers (first⁻¹ * second)) W) ≠ 2) :
    first = second ∨ (Nat.card U = 4 ∧ L ≤ U) := by
  let D := commutatorAction (Subgroup.zpowers first) W
  let D' := commutatorAction (Subgroup.zpowers second) W
  let difference := first⁻¹ * second
  let B := commutatorAction (Subgroup.zpowers difference) W
  change Nat.card B ≠ 2 at hno
  have hSpos : 1 < Nat.card S := (Subgroup.one_lt_card_iff_ne_bot S).mpr hS
  by_cases heq : D = D'
  · left
    have hBD : B ≤ D := by
      apply displacement_le_of_pointwise
      intro w
      have hx : w⁻¹ * second w ∈ D := by
        rw [heq]
        change _ ∈ commutatorAction (Subgroup.zpowers second) W
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨⟨second, Subgroup.mem_zpowers _⟩, w, rfl⟩
      have hy : (first⁻¹ (second w))⁻¹ * second w ∈ D := by
        change _ ∈ commutatorAction (Subgroup.zpowers first) W
        rw [commutatorAction_eq_closure]
        have hh : (first⁻¹ (second w))⁻¹ * first (first⁻¹ (second w)) ∈
            Subgroup.closure {x : W | ∃ a : Subgroup.zpowers first, ∃ v : W,
              x = v⁻¹ * a • v} :=
          Subgroup.subset_closure ⟨⟨first, Subgroup.mem_zpowers _⟩,
            first⁻¹ (second w), rfl⟩
        simpa only [MulAut.apply_inv_self] using hh
      have hh := D.mul_mem hx (D.inv_mem hy)
      change w⁻¹ * first⁻¹ (second w) ∈ D
      simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hh
    have hproper : D ⊓ C ≠ D := by
      intro hh
      have hSC : S ≤ C := hSfirst.trans (hh.symm.le.trans inf_le_right)
      exact hS (bot_unique ((le_inf hSU hSC).trans hUC.le_bot))
    have hcard : Nat.card B ≤ 2 :=
      (Subgroup.card_le_of_le (le_inf hBD hdelta)).trans
        (proper_subgroup_card_le_two_of_card_four D (D ⊓ C) hfirst inf_le_left hproper)
    have hBbot : B = ⊥ := Subgroup.card_eq_one.mp (by have := Nat.card_pos (α := B); omega)
    have hfix := actsTrivially_of_commutatorAction_eq_bot hBbot
    have hdifference : difference = 1 := by
      ext w
      exact hfix ⟨difference, Subgroup.mem_zpowers _⟩ w
    exact inv_mul_eq_one.mp hdifference
  · right
    have hproper : D ⊓ D' ≠ D := by
      intro hh
      have hle : D ≤ D' := hh ▸ inf_le_right
      exact heq (Subgroup.eq_of_le_of_card_ge hle (by rw [hfirst, hsecond]))
    have hcommon : Nat.card (D ⊓ D' : Subgroup W) ≤ 2 :=
      proper_subgroup_card_le_two_of_card_four D (D ⊓ D') hfirst inf_le_left hproper
    have hScard : Nat.card S = 2 := by
      have hh := (Subgroup.card_le_of_le (le_inf hSfirst hSsecond)).trans hcommon
      omega
    have hScommon : S = D ⊓ D' :=
      Subgroup.eq_of_le_of_card_ge (le_inf hSfirst hSsecond) (by omega)
    have hLcommon : L = D ⊓ D' :=
      Subgroup.eq_of_le_of_card_ge (le_inf hLfirst hLsecond) (by omega)
    exact ⟨by rw [hU, hScard]; decide, hLcommon.trans hScommon.symm ▸ hSU⟩
