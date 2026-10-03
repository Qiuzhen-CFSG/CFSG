module
public import ABG.ChapterIII.Section2.ThreePrincipalData
public import Theory.Character.InvolutionSum
public import Theory.Character.InvolutionRootRestriction

/-!
# The principal-character combination for the order formula

The combination 1 − χ₁ + χ⁽²⁾ vanishes on odd-order elements and on the
involution section. Restriction to roots of x and induction transfer its
involution-pair pairing to C_G(x). The global pairing is
|G|/|C_G(x)|² times (1 − 9/f₁ + 4/(f₁ − 1)).

This module proves the global and transfer sides for arbitrary supplied
principal-block data. The local evaluation still requires local group geometry.

Source: Alperin–Brauer–Gorenstein, III.7 equation (8), article pp.103–104,
specialized to characteristic three and the principal block.
-/

namespace ABG.ThreePrincipalData
open Theory.Character
open ModularBlock.PrincipalBlockConstruction ModularBlock.CompatibleBrauerBlock
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G] {x : G} (c : ABG.ThreePrincipalData G x)

/-- The characteristic-three column combination used in ABG III.7 (8). -/
@[expose] public def orderFunction : ClassFunction G :=
  ofConjClassFunction (c.χ 0) - ofConjClassFunction (c.χ 1) + ofConjClassFunction (c.χ 5)

/-- Restriction to roots of the involution, extended by zero within its centralizer. -/
@[expose] public def localOrderFunction : ClassFunction (Subgroup.centralizer ({x} : Set G)) :=
  involutionRootRestriction x c.orderFunction

public theorem orderFunction_odd (g : G) (hg : Odd (orderOf g)) : c.orderFunction g = 0 := by
  have h := c.odd_exceptional g hg 0
  change c.χ 5 (ConjClasses.mk g) + 1 = c.χ 1 (ConjClasses.mk g) at h
  change c.χ 0 (ConjClasses.mk g) - c.χ 1 (ConjClasses.mk g) +
    c.χ 5 (ConjClasses.mk g) = 0
  rw [c.principal_eq]
  simp only [ordinaryPrincipalCharacter_apply]
  linear_combination h

public theorem orderFunction_involution_section
    (r : Subgroup.centralizer ({x} : Set G)) (hr : Odd (orderOf r)) :
    c.orderFunction (x * (r : G)) = 0 := by
  change c.χ 0 _ - c.χ 1 _ + c.χ 5 _ = 0
  simp only [χ, c.involution_section r hr, threePrincipalInvolutionSection, Matrix.cons_val]
  ring

/-- Evaluation on each cyclic two-singular section. -/
public theorem orderFunction_cyclic_section (h : ℤ) (hh : ¬ 4 ∣ h)
    (r : Subgroup.centralizer ({c.generator ^ h} : Set G)) (hr : Odd (orderOf r)) :
    c.orderFunction (c.generator ^ h * (r : G)) =
      2 - (c.root ^ (2*h) + (-c.root) ^ (-(2*h))) := by
  change c.χ 0 _ - c.χ 1 _ + c.χ 5 _ = _
  simp only [χ, c.cyclic_section h hh r hr, threePrincipalCyclicSection, Matrix.cons_val]
  ring

/-- The order-four section contributes the constant four. -/
public theorem orderFunction_order_four_section (r : Subgroup.centralizer ({c.generator ^ (2 : ℤ)} : Set G))
    (hr : Odd (orderOf r)) : c.orderFunction (c.generator ^ (2 : ℤ) * (r : G)) = 4 := by
  have h4 : c.root ^ (4 : ℕ) = -1 :=
    (c.root_primitive.pow (by decide) (by decide : 8 = 4 * 2)).eq_neg_one_of_two_right
  change c.χ 0 _ - c.χ 1 _ + c.χ 5 _ = _
  simp only [χ, c.cyclic_section 2 (by norm_num) r hr, threePrincipalCyclicSection,
    Matrix.cons_val]
  norm_num [zpow_neg, h4]


/-- The column combination is conjugacy invariant. -/
public theorem orderFunction_isClassFunction : IsClassFunction c.orderFunction :=
  ofConjClassFunction_isClassFunction (c.χ 0 - c.χ 1 + c.χ 5)

/-- Recover the global combination by induction from the root restriction. -/
public theorem induced_localOrderFunction (hx : orderOf x = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u x) :
    inducedClassFunction (Subgroup.centralizer ({x} : Set G))
      c.localOrderFunction = c.orderFunction :=
  induced_involutionRootRestriction x hx hfuse c.orderFunction
    c.orderFunction_isClassFunction c.orderFunction_odd

/-- The root transfer retains the pairing with actual involution pairs. -/
public theorem orderFunction_pairing_eq_local (hx : orderOf x = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u x) :
    scalarProduct G c.orderFunction (fun a => (involutionPairCount a : ℂ)) =
      scalarProduct (Subgroup.centralizer ({x} : Set G)) c.localOrderFunction
        (fun a => (involutionPairCount a : ℂ)) := by
  rw [← c.induced_localOrderFunction hx hfuse]
  convert scalarProduct_induced_involutionPairCount x hx c.localOrderFunction
    (involutionRootRestriction_supported x c.orderFunction) using 1
  congr 1
  exact Subsingleton.elim _ _

private theorem row_irreducible (i : Fin 8) :
    IsIrreducibleCharacter (ofConjClassFunction (c.χ i)) := by
  obtain ⟨n, ρ, hρ⟩ := (c.irreducible i).1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using (c.irreducible i).2
  · rw [hρ]
    rfl

/-- The global pairing, before evaluating the corresponding local count. -/
public theorem orderFunction_pairing (hx : orderOf x = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u x) :
    scalarProduct G c.orderFunction (fun a => (involutionPairCount a : ℂ)) =
      (Nat.card G : ℂ) / Nat.card (Subgroup.centralizer ({x} : Set G)) ^ 2 *
        (1 - 9 / (c.degree 0 : ℂ) + 4 / ((c.degree 0 : ℂ) - 1)) := by
  have h (i : Fin 8) := scalarProduct_irreducible_involutionPairCount_of_fusion
    x hx hfuse _ (c.row_irreducible i)
  rw [orderFunction, scalarProduct_add_left, _root_.scalarProduct_sub_left, h 0, h 1, h 5]
  simp only [ofConjClassFunction_apply, c.involution_values]
  have hd (i : Fin 8) := c.degree_value i
  change ∀ i : Fin 8, c.χ i (ConjClasses.mk 1) = _ at hd
  simp only [hd, Matrix.cons_val]
  have he : (c.degree 4 : ℂ) = (c.degree 0 : ℂ) - 1 := by
    have := c.degree_identities.2.2
    have hh : (c.degree 4 : ℂ) + 1 = c.degree 0 := by exact_mod_cast this
    linear_combination hh
  rw [he]
  ring

end
end ABG.ThreePrincipalData
