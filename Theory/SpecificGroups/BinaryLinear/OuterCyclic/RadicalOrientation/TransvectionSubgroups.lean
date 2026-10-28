module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic

/-!
# Common image or common kernel for binary transvection subgroups

A subgroup whose nonidentity elements are transvections is contained in a
point radical or a hyperplane radical. Here the hyperplane radical is the
published `radical f.ker`: it fixes the kernel pointwise and acts trivially
on the quotient.

For two transvections with different nonzero forms, choose vectors on which
the forms take the values (1, 0) and (0, 1). Their product has displacements
`v` and `w + f w • v`. If the product is the identity or a transvection,
these force `v = w`. Thus every pair has the same direction or the same
form. If the subgroup is not contained in the point radical of one chosen
transvection, a second direction exists. Comparing every transvection with
these two shows that all forms coincide. The identity subgroup is handled
separately.

This is the geometric containment ingredient for the binary automorphism
argument associated with GLS3, Theorem 2.5.12(b–e,i) and §2.7, especially the
matrix realization in `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
Maximality, equality of radicals, and automorphism classification are left
to the consuming orientation argument.
-/

public section

namespace BinaryLinear.OuterCyclic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (binary_cases a).resolve_left ha

private theorem exists_value_one {f : V →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) :
    ∃ x, f x = 1 := by
  have h : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := h
  exact ⟨x, scalar_one hx⟩

/-- Different nonzero binary forms can be separated by a vector. -/
private theorem exists_one_zero {f g : V →ₗ[ZMod 2] ZMod 2}
    (hf : f ≠ 0) (hfg : f ≠ g) : ∃ x, f x = 1 ∧ g x = 0 := by
  by_contra! h
  have h1 (x : V) (hx : f x = 1) : g x = 1 := scalar_one (h x hx)
  obtain ⟨y, hy⟩ := exists_value_one hf
  have hgy := h1 y hy
  apply hfg
  ext x
  rcases binary_cases (f x) with hx | hx
  · rcases binary_cases (g x) with hgx | hgx
    · exact hx.trans hgx.symm
    · have hsum := h1 (x + y) (by simp [hx, hy])
      simp only [map_add, hgx, hgy] at hsum
      exact False.elim (by revert hsum; decide)
  · exact hx.trans (h1 x hx).symm

/-- Two transvections whose product is trivial or a transvection share a direction
or a form. -/
private theorem transvection_pair {v w : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfv : f v = 0) (hgw : g w = 0)
    (hprod : transvection v f hfv * transvection w g hgw = 1 ∨
      IsTransvection (transvection v f hfv * transvection w g hgw)) :
    v = w ∨ f = g := by
  by_cases hfg : f = g
  · exact Or.inr hfg
  left
  obtain ⟨x, hfx, hgx⟩ := exists_one_zero hf hfg
  obtain ⟨y, hgy, hfy⟩ := exists_one_zero hg (Ne.symm hfg)
  have hx : (transvection v f hfv * transvection w g hgw) x = x + v := by
    change (x + g x • w) + f (x + g x • w) • v = x + v
    simp [hgx, hfx]
  have hy : (transvection v f hfv * transvection w g hgw) y =
      y + (w + f w • v) := by
    change (y + g y • w) + f (y + g y • w) • v = y + (w + f w • v)
    simp [hgy, hfy, add_assoc]
  rcases hprod with hprod | hprod
  · have hz : x + v = x := by simpa [hprod] using hx.symm
    exact False.elim (hv (add_eq_left.mp hz))
  · obtain ⟨u, k, _, _, hku, he⟩ := hprod
    have hx' : v = k x • u := by
      have h := hx
      rw [he] at h
      change x + k x • u = x + v at h
      exact (add_left_cancel h).symm
    have hkx : k x = 1 := by
      apply scalar_one
      intro hz
      exact hv (by simpa [hz] using hx')
    have hvu : v = u := by simpa [hkx] using hx'
    have hy' : w + f w • v = k y • v := by
      have h := hy
      rw [he] at h
      change y + k y • u = y + (w + f w • v) at h
      rw [← hvu] at h
      exact (add_left_cancel h).symm
    have hwv : w = (k y - f w) • v := by
      rw [sub_smul]
      exact eq_sub_iff_add_eq.mpr hy'
    rcases binary_cases (k y - f w) with hz | ho
    · exact False.elim (hw (by simpa [hz] using hwv))
    · simpa [ho] using hwv.symm

private theorem transvection_pair_of_mem (H : Subgroup (BinaryLinear.GL V))
    (hH : ∀ t ∈ H, t ≠ 1 → IsTransvection t)
    {v w : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfv : f v = 0) (hgw : g w = 0)
    (hs : transvection v f hfv ∈ H) (ht : transvection w g hgw ∈ H) :
    v = w ∨ f = g := by
  apply transvection_pair hv hw hf hg hfv hgw
  by_cases he : transvection v f hfv * transvection w g hgw = 1
  · exact Or.inl he
  · exact Or.inr (hH _ (H.mul_mem hs ht) he)

/-- A binary transvection subgroup has a common image line or a common fixed
hyperplane. This proves containment, without a maximality assumption. -/
theorem transvectionSubgroup_le_point_or_hyperplane {n : ℕ} (hn : n = 4 ∨ n = 5)
    (H : Subgroup (LinearGroup n)) (hH : ∀ t ∈ H, t ≠ 1 → IsTransvection t) :
    (∃ v : Space n, v ≠ 0 ∧ H ≤ pointRadical n v) ∨
    (∃ f : Space n →ₗ[ZMod 2] ZMod 2, f ≠ 0 ∧ H ≤ hyperplaneRadical n f) := by
  classical
  by_cases hH0 : H = ⊥
  · refine Or.inl ⟨fun _ => 1, ?_, hH0 ▸ bot_le⟩
    intro hz
    have h := congrFun hz (⟨0, by omega⟩ : Fin n)
    exact one_ne_zero h
  have hs : ∃ s ∈ H, s ≠ 1 := by
    by_contra! h
    apply hH0
    exact le_antisymm (fun t ht => Subgroup.mem_bot.mpr (h t ht)) bot_le
  obtain ⟨s, hs, hs1⟩ := hs
  obtain ⟨v, f, hv, hf, hfv, rfl⟩ := hH s hs hs1
  by_cases hpoint : H ≤ pointRadical n v
  · exact Or.inl ⟨v, hv, hpoint⟩
  have ht : ∃ t ∈ H, t ∉ pointRadical n v := by
    simpa only [SetLike.le_def, not_forall, Classical.not_imp, exists_prop] using hpoint
  obtain ⟨t, ht, htp⟩ := ht
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    exact htp (pointRadical n v).one_mem
  obtain ⟨w, g, hw, hg, hgw, rfl⟩ := hH t ht ht1
  have hvw : v ≠ w := by
    intro he
    subst w
    exact htp (transvection_mem (Submodule.mem_span_singleton_self v)
      (Submodule.span_le.mpr (by simpa using hgw)))
  have hfg : f = g :=
    (transvection_pair_of_mem H hH hv hw hf hg hfv hgw hs ht).resolve_left hvw
  refine Or.inr ⟨f, hf, ?_⟩
  intro u hu
  by_cases hu1 : u = 1
  · exact hu1 ▸ (hyperplaneRadical n f).one_mem
  obtain ⟨z, k, hz, hk, hkz, rfl⟩ := hH u hu hu1
  have hfk : f = k := by
    rcases transvection_pair_of_mem H hH hv hz hf hk hfv hkz hs hu with hvz | hfk
    · have hwz : w ≠ z := by
        intro he
        exact hvw (hvz.trans he.symm)
      exact hfg.trans
        ((transvection_pair_of_mem H hH hw hz hg hk hgw hkz ht hu).resolve_left hwz)
    · exact hfk
  subst k
  exact transvection_mem (show z ∈ f.ker from hkz) le_rfl

end BinaryLinear.OuterCyclic
