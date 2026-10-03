module

public import Theory.Character.TwoSectionMass
public import Theory.Character.RationalPower

/-!
# Inverting a two-section

Inversion identifies the centralizers of an element and its inverse and permutes
their odd-order elements. Character values at inverse elements are complex
conjugates, so the actual local normalized sums of squared norms agree. For an
integer-valued character the values themselves agree as well.

This supplies the inverse-section step in the contribution calculation of
Fong (1967), printed pp. 73–74, without decomposition-number assumptions.
-/

public section
noncomputable section
open scoped BigOperators
namespace Theory.Character
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Inversion preserves the actual section mass whenever it preserves the
squared norm of the function. No order assumption on the section base is needed. -/
theorem twoSectionMass_inv_of_normSq_inv (χ : ClassFunction G) (u : G)
    (hχ : ∀ g, Complex.normSq (χ g⁻¹) = Complex.normSq (χ g)) :
    twoSectionMass χ u⁻¹ = twoSectionMass χ u := by
  classical
  let : Fintype (Subgroup.centralizer ({u⁻¹} : Set G)) := Fintype.ofFinite _
  let : Fintype (Subgroup.centralizer ({u} : Set G)) := Fintype.ofFinite _
  have hc : Subgroup.centralizer ({u⁻¹} : Set G) = Subgroup.centralizer ({u} : Set G) := by
    ext x
    simpa only [Subgroup.mem_centralizer_singleton_iff, commute_iff_eq] using
      (Commute.inv_right_iff (a := x) (b := u))
  unfold twoSectionMass
  rw [show Nat.card (Subgroup.centralizer ({u⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({u} : Set G)) by rw [hc]]
  congr 1
  let e : Subgroup.centralizer ({u⁻¹} : Set G) ≃ Subgroup.centralizer ({u} : Set G) :=
    (Equiv.setCongr (congrArg (fun H : Subgroup G => (H : Set G)) hc)).trans
      (Equiv.inv _)
  apply Fintype.sum_equiv e
  intro v
  change (if Odd (orderOf v) then Complex.normSq (χ (u⁻¹ * (v : G))) else 0) =
    if Odd (orderOf ((⟨(v : G), by rw [← hc]; exact v.property⟩ :
        Subgroup.centralizer ({u} : Set G))⁻¹))
      then Complex.normSq (χ (u * (v : G)⁻¹)) else 0
  simp only [orderOf_inv, ← Subgroup.orderOf_coe]
  split_ifs
  · have hv : Commute (v : G) u := Subgroup.mem_centralizer_singleton_iff.mp
      (show (v : G) ∈ Subgroup.centralizer ({u} : Set G) by
        rw [← hc]
        exact v.property)
    rw [← hχ (u⁻¹ * (v : G))]
    simp only [mul_inv_rev, inv_inv]
    rw [hv.inv_left.eq]
  · rfl

/-- A character has equal masses on inverse sections. -/
theorem twoSectionMass_inv {χ : ClassFunction G} (hχ : IsCharacter χ) (u : G) :
    twoSectionMass χ u⁻¹ = twoSectionMass χ u := by
  apply twoSectionMass_inv_of_normSq_inv
  obtain ⟨n, ρ, rfl⟩ := hχ
  intro g
  rw [Representation.representation_character_inv_eq_star_character]
  exact Complex.normSq_conj _

/-- Integer character values and actual masses both agree on inverse sections. -/
theorem inverse_section_value_and_mass {χ : ClassFunction G} (hχ : IsCharacter χ)
    (u : G) (hint : ∃ a : ℤ, χ u = (a : ℂ)) :
    χ u⁻¹ = χ u ∧ twoSectionMass χ u⁻¹ = twoSectionMass χ u :=
  ⟨hχ.inv_eq_of_integer_value u hint, twoSectionMass_inv hχ u⟩

end Theory.Character
