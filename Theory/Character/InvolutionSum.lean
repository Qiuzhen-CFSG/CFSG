module
public import Theory.Character.InvolutionRootPairing
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Character sums over involutions

Involution sums transport along group equivalences. When all involutions are
conjugate to a fixed involution, orbit–stabilizer evaluates the sum as the
group order divided by the centralizer order, times the character value.
These counting identities supply the inputs to Wong's involution-pair formula.

Source: orbit–stabilizer; Wong (1964), Lemma 4(iii), p.98, and the
involution-sum calculation on p.100, DOI 10.1017/S1446788700022771.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

namespace Theory.Character

/-- Write the sum over involutions as a filtered sum over the group. -/
public theorem involutionSum_eq_sum_ite {G : Type*} [Group G] [Fintype G]
    (f : ClassFunction G) :
    involutionSum f = ∑ g : G, if orderOf g = 2 then f g else 0 := by
  rw [involutionSum]
  calc
    _ = ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 2), f g :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = _ := Finset.sum_filter _ _

/-- Transport the actual involution sum, including the order-two condition. -/
public theorem involutionSum_comp_mulEquiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : H ≃* G) (f : ClassFunction G) :
    involutionSum (fun h => f (e h)) = involutionSum f := by
  rw [involutionSum_eq_sum_ite, involutionSum_eq_sum_ite]
  exact Fintype.sum_equiv e.toEquiv _ _ fun h => by
    change (if orderOf h = 2 then f (e h) else 0) =
      if orderOf (e h) = 2 then f (e h) else 0
    rw [show orderOf (e h) = orderOf h from
      orderOf_injective e.toMonoidHom e.injective h]

/-- If involutions form one conjugacy class, its cardinality times the
centralizer order is the group order. -/
public theorem card_involutions_mul_card_centralizer
    {G : Type*} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t) :
    Nat.card {u : G // orderOf u = 2} *
      Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card G := by
  let e : {u : G // orderOf u = 2} ≃ (ConjClasses.mk t).carrier :=
    Equiv.subtypeEquivRight fun u => by
      change orderOf u = 2 ↔ IsConj t u
      refine ⟨fun h => (hfuse u h).symm, fun h => ?_⟩
      obtain ⟨g, rfl⟩ := isConj_iff.mp h
      simpa using (orderOf_injective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective t).trans ht
  rw [Nat.card_congr e]
  have hc := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) t
  have he : Nat.card (MulAction.stabilizer (ConjAct G) t) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
    apply Nat.card_congr
    exact {
      toFun := fun g => ⟨ConjAct.ofConjAct g.val, by
        simpa only [Subgroup.mem_centralizer_singleton_iff,
          MulAction.mem_stabilizer_iff, ConjAct.smul_def,
          mul_inv_eq_iff_eq_mul] using g.property⟩
      invFun := fun g => ⟨ConjAct.toConjAct g.val, by
        simpa only [Subgroup.mem_centralizer_singleton_iff,
          MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul,
          mul_inv_eq_iff_eq_mul] using g.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [ConjAct.orbit_eq_carrier_conjClasses, ← Nat.card_eq_fintype_card,
    he, Nat.card_congr (ConjAct.ofConjAct (G := G)).toEquiv] using hc

/-- Evaluate any class function on a single class of involutions. -/
public theorem involutionSum_of_fusion
    {G : Type*} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t)
    (f : ClassFunction G) (hf : IsClassFunction f) :
    involutionSum f = (Nat.card G : ℂ) /
      Nat.card (Subgroup.centralizer ({t} : Set G)) * f t := by
  have he (u : {u : G // orderOf u = 2}) : f u = f t := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (hfuse u u.property)
    rw [← hg]
    exact (hf u g).symm
  have hc : (Nat.card {u : G // orderOf u = 2} : ℂ) *
      Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card G := by
    exact_mod_cast card_involutions_mul_card_centralizer t ht hfuse
  have hn : (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({t} : Set G))).ne'
  simp only [involutionSum, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  rw [← hc, mul_div_cancel_right₀ _ hn]

/-- With one class of involutions, the pair-count coefficient depends only
on the degree, the involution value, and its centralizer order. -/
public theorem scalarProduct_irreducible_involutionPairCount_of_fusion
    {G : Type*} [Group G] [Fintype G] (t : G) (ht : orderOf t = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G χ (fun a => (involutionPairCount a : ℂ)) =
      (Nat.card G : ℂ) / Nat.card (Subgroup.centralizer ({t} : Set G)) ^ 2 *
        χ t ^ 2 / χ 1 := by
  have hclass : IsClassFunction χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    intro a g
    exact Representation.char_conj ρ a g
  rw [scalarProduct_irreducible_involutionPairCount χ hχ,
    involutionSum_of_fusion t ht hfuse χ hclass]
  have hg : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  field_simp

end Theory.Character
