module

public import Theory.GroupTheory.SubgroupEnumeration
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Double-coset coverage from short transition tables

Let `K` and a family of additional elements generate a finite group. A union
of `K` double cosets containing the identity is the whole group if it is
closed under right multiplication by the additional elements. To check this,
it suffices to test `r * t * g`, where `t` runs through left cosets of
`K ∩ g K g⁻¹` in `K`. The remaining factor passes across `g` into `K`.

The transversal itself can be certified by generator transitions. Finiteness
allows positive generator words throughout; no inverse tables are required.
All transition equations and all subgroup memberships remain proof obligations.

Source: the elementary word-induction proof of double-coset enumeration;
compare the right-coset certificates in `SubgroupEnumeration`.
-/

namespace Theory.GroupTheory.DoubleCosetTransitions
public section

variable {G : Type*} [Group G] {ρ α τ : Type*}

/-- Membership in the union of a specified family of double cosets. -/
@[expose] def Covered (K : Subgroup G) (rep : ρ → G) (x : G) : Prop :=
  ∃ j u v, u ∈ K ∧ v ∈ K ∧ x = u * rep j * v

theorem Covered.mul_left {K : Subgroup G} {rep : ρ → G} {x u : G}
    (hx : Covered K rep x) (hu : u ∈ K) : Covered K rep (u * x) := by
  obtain ⟨j, v, w, hv, hw, rfl⟩ := hx
  exact ⟨j, u * v, w, K.mul_mem hu hv, hw, by simp only [mul_assoc]⟩

theorem Covered.mul_right {K : Subgroup G} {rep : ρ → G} {x v : G}
    (hx : Covered K rep x) (hv : v ∈ K) : Covered K rep (x * v) := by
  obtain ⟨j, u, w, hu, hw, rfl⟩ := hx
  exact ⟨j, u, w * v, hu, K.mul_mem hw hv, mul_assoc _ _ _⟩

/-- Positive generator transitions certify a left transversal of the
intersection with a conjugate. Repetitions in the transversal are allowed. -/
theorem conjugate_split_of_steps [Finite G] (K : Subgroup G)
    (gen : α → G) (hgen : Subgroup.closure (Set.range gen) = K)
    (g : G) (transversal : τ → G)
    (hbase : ∃ j, transversal j = 1)
    (hstep : ∀ i j, ∃ k c, c ∈ K ∧ g⁻¹ * c * g ∈ K ∧
      gen i * transversal j = transversal k * c)
    {x : G} (hx : x ∈ K) :
    ∃ j c, c ∈ K ∧ g⁻¹ * c * g ∈ K ∧ x = transversal j * c := by
  have hx' : x ∈ Submonoid.closure (Set.range gen) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, hgen]
    exact hx
  clear hx
  induction hx' using Submonoid.closure_induction_left with
  | one =>
      obtain ⟨j, hj⟩ := hbase
      exact ⟨j, 1, K.one_mem, by simp, by simp [hj]⟩
  | mul_left y hy x _ ih =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, c, hc, hcg, rfl⟩ := ih
      obtain ⟨k, d, hd, hdg, he⟩ := hstep i j
      refine ⟨k, d * c, K.mul_mem hd hc, ?_, ?_⟩
      · simpa only [mul_assoc, mul_inv_cancel_left] using K.mul_mem hdg hcg
      · rw [← mul_assoc, he, mul_assoc]

/-- A short middle transversal reduces closure under each additional
generator to finitely many double-coset transitions. -/
theorem cover_of_transitions [Finite G] (K : Subgroup G) (rep : ρ → G)
    (gen : α → G)
    (hgen : Subgroup.closure ((K : Set G) ∪ Set.range gen) = ⊤)
    (hbase : ∃ j, rep j = 1) (transversal : α → τ → G)
    (hsplit : ∀ i s, s ∈ K → ∃ t c, c ∈ K ∧ (gen i)⁻¹ * c * gen i ∈ K ∧
      s = transversal i t * c)
    (hstep : ∀ j i t, Covered K rep (rep j * transversal i t * gen i)) :
    SubgroupEnumeration.DoubleCosetCover K rep := by
  have hmonoid : Submonoid.closure ((K : Set G) ∪ Set.range gen) = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, hgen]
    rfl
  intro x
  change Covered K rep x
  refine Submonoid.induction_of_closure_eq_top_right
    (motive := Covered K rep) hmonoid x ?_ ?_
  · obtain ⟨j, hj⟩ := hbase
    exact ⟨j, 1, 1, K.one_mem, K.one_mem, by simp [hj]⟩
  · intro x y hy hx
    rcases hy with hy | ⟨i, rfl⟩
    · exact hx.mul_right hy
    · obtain ⟨j, u, s, hu, hs, rfl⟩ := hx
      obtain ⟨t, c, _, hcg, rfl⟩ := hsplit i s hs
      have h := ((hstep j i t).mul_left hu).mul_right hcg
      simpa only [mul_assoc, mul_inv_cancel_left] using h

end
end Theory.GroupTheory.DoubleCosetTransitions
