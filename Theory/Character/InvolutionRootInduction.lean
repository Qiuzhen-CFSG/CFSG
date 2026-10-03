module
public import Theory.Character.BrauerSuzuki
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Induction on roots of a fixed involution

For an involution t in a finite group G, let H be its centralizer. Consider
functions on H supported on the elements a whose cyclic subgroup contains t.
Induction to G preserves their scalar product. On such roots the induced
function equals its original value; away from G-conjugates of roots it is zero.
These identities apply in particular to generalized characters when the later
character construction supplies them. No generalized-character hypothesis is
needed for the finite-sum identities proved here.

The key reduction preserves the actual conjugator: if a and g⁻¹ag both have t
in their cyclic subgroups, uniqueness of the involution in a cyclic group forces
g to centralize t. Consequently the root support has disjoint conjugates outside
H. In the existing Brauer--Suzuki pairing expansion all such terms vanish; the
remaining H terms give exactly the original scalar product. The same reduction
proves the pointwise induction formula. Fintype instances for subgroup sums
remain local and use the same convention as the imported induction expansion.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2, J. Austral. Math. Soc. 4 (1964),90–112, Lemma4(i),(ii),
article98. These are the induction inputs to his actual GL2(3)-centralizer
recognition, Appendix Theorem6. DOI:10.1017/S1446788700022771.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

private theorem root_conjugator_mem_centralizer
    {G : Type*} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    (a g : G) (ha : t ∈ Subgroup.zpowers a)
    (hga : t ∈ Subgroup.zpowers (g⁻¹ * a * g)) :
    g ∈ Subgroup.centralizer ({t} : Set G) := by
  let e := MulAut.conj g⁻¹
  have he : e a = g⁻¹ * a * g := by simp [e]
  have het : e t ∈ Subgroup.zpowers (g⁻¹ * a * g) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, ?_⟩
    rw [← he, ← map_zpow, hn]
  have horder : orderOf (e t) = 2 :=
    (orderOf_injective e.toMonoidHom e.injective t).trans ht
  have ht' : orderOf (⟨t, hga⟩ : Subgroup.zpowers (g⁻¹ * a * g)) = 2 := by
    simpa only [← Subgroup.orderOf_coe] using ht
  have het' : orderOf (⟨e t, het⟩ : Subgroup.zpowers (g⁻¹ * a * g)) = 2 := by
    simpa only [← Subgroup.orderOf_coe] using horder
  have heqt := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two het' ht')
  have hc : g⁻¹ * t * g = t := by simpa [e, MulAut.conj_apply] using heqt
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun x : G => g * x) hc
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh.symm

/-- Induction preserves the scalar product on functions supported on roots of
an actual involution. Only the second function needs class invariance. -/
public theorem scalarProduct_inducedClassFunction_involutionRoots
    {G : Type*} [Group G] [Fintype G] (t : G) (ht : orderOf t = 2)
    (φ ψ : ClassFunction (Subgroup.centralizer ({t} : Set G)))
    (hψ : IsClassFunction ψ)
    (hφD : ∀ a : Subgroup.centralizer ({t} : Set G), t ∉ Subgroup.zpowers (a : G) → φ a = 0)
    (hψD : ∀ a : Subgroup.centralizer ({t} : Set G), t ∉ Subgroup.zpowers (a : G) → ψ a = 0) :
    scalarProduct G
      (inducedClassFunction (Subgroup.centralizer ({t} : Set G)) φ)
      (inducedClassFunction (Subgroup.centralizer ({t} : Set G)) ψ) =
    scalarProduct (Subgroup.centralizer ({t} : Set G)) φ ψ := by
  classical
  let H := Subgroup.centralizer ({t} : Set G)
  have hsummand (g : G) (a : H) :
      pairingSummand H φ ψ g a = if g ∈ H then φ a * star (ψ a) else 0 := by
    by_cases hg : g ∈ H
    · rw [if_pos hg]
      have ha : g⁻¹ * (a : G) * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) a.property) hg
      rw [pairingSummand, dif_pos ha]
      have hconj : (⟨g⁻¹ * (a : G) * g, ha⟩ : H) =
          (⟨g, hg⟩ : H)⁻¹ * a * (⟨g, hg⟩ : H) := rfl
      rw [hconj]
      have hψconj := hψ a (⟨g, hg⟩ : H)⁻¹
      simpa only [inv_inv] using congrArg (fun x : ℂ => φ a * star x) hψconj
    · rw [if_neg hg]
      by_cases ha : t ∈ Subgroup.zpowers (a : G)
      · unfold pairingSummand
        split_ifs with hconj
        · have hnot : t ∉ Subgroup.zpowers (g⁻¹ * (a : G) * g) := by
            intro h
            exact hg (root_conjugator_mem_centralizer t ht a g ha h)
          rw [hψD _ hnot, star_zero, mul_zero]
        · rfl
      · unfold pairingSummand
        split_ifs <;> simp [hφD a ha]
  change scalarProduct G (inducedClassFunction H φ) (inducedClassFunction H ψ) =
    scalarProduct H φ ψ
  rw [pairing_induced_expand]
  simp_rw [hsummand]
  have hsum : (∑ g : G, ∑ a : H, if g ∈ H then φ a * star (ψ a) else 0) =
      (Nat.card H : ℂ) * ∑ a : H, φ a * star (ψ a) := by
    simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (F := inferInstance) (p := fun g : G => g ∈ H) _ (by simp) (fun _ : G => ∑ a : H, φ a * star (ψ a))]
    simp [← Nat.card_eq_fintype_card]
  rw [hsum]
  change (Nat.card H : ℂ)⁻¹ * (Nat.card H : ℂ)⁻¹ *
    ((Nat.card H : ℂ) * ∑ a : H, φ a * star (ψ a)) =
      (Nat.card H : ℂ)⁻¹ * ∑ a : H, φ a * star (ψ a)
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  field_simp

/-- At a root of the fixed involution, induction retains the exact original value. -/
public theorem inducedClassFunction_involutionRoots_apply
    {G : Type*} [Group G] [Fintype G] (t : G) (ht : orderOf t = 2)
    (φ : ClassFunction (Subgroup.centralizer ({t} : Set G)))
    (hφ : IsClassFunction φ)
    (hφD : ∀ a : Subgroup.centralizer ({t} : Set G),
      t ∉ Subgroup.zpowers (a : G) → φ a = 0)
    (a : Subgroup.centralizer ({t} : Set G)) (ha : t ∈ Subgroup.zpowers (a : G)) :
    inducedClassFunction (Subgroup.centralizer ({t} : Set G)) φ a = φ a := by
  classical
  let H := Subgroup.centralizer ({t} : Set G)
  have hsummand (g : G) :
      (if hg : g⁻¹ * (a : G) * g ∈ H then φ ⟨g⁻¹ * (a : G) * g, hg⟩ else 0) =
      if g ∈ H then φ a else 0 := by
    by_cases hg : g ∈ H
    · rw [if_pos hg]
      have hga : g⁻¹ * (a : G) * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) a.property) hg
      rw [dif_pos hga]
      have hconj : (⟨g⁻¹ * (a : G) * g, hga⟩ : H) =
          (⟨g, hg⟩ : H)⁻¹ * a * (⟨g, hg⟩ : H) := rfl
      rw [hconj]
      simpa only [inv_inv] using hφ a (⟨g, hg⟩ : H)⁻¹
    · rw [if_neg hg]
      split_ifs with hga
      · apply hφD
        intro h
        exact hg (root_conjugator_mem_centralizer t ht a g ha h)
      · rfl
  change inducedClassFunction H φ a = φ a
  rw [inducedClassFunction]
  simp_rw [hsummand]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (F := inferInstance) (p := fun g : G => g ∈ H) _ (by simp) (fun _ : G => φ a)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  exact inv_mul_cancel_left₀ hcard (φ a)

/-- The induced function vanishes away from conjugates of the root support. -/
public theorem inducedClassFunction_involutionRoots_eq_zero
    {G : Type*} [Group G] [Fintype G] (t : G)
    (φ : ClassFunction (Subgroup.centralizer ({t} : Set G)))
    (hφD : ∀ a : Subgroup.centralizer ({t} : Set G),
      t ∉ Subgroup.zpowers (a : G) → φ a = 0)
    (a : G) (ha : ∀ g : G, t ∉ Subgroup.zpowers (g⁻¹ * a * g)) :
    inducedClassFunction (Subgroup.centralizer ({t} : Set G)) φ a = 0 := by
  classical
  rw [inducedClassFunction]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro g _
  split_ifs with h
  · exact hφD _ (ha g)
  · rfl
