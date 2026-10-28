module

public import Theory.Representation.PSL3Two.FourGroupGeometry
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Natural-plus-dual fixed spaces of inner four-groups in Aut(SL₃(2))

Every inner elementary four-group fixes eight vectors on the sum of the natural
module and its literal dual. Its inner pointwise stabilizer is the four-group
itself. We lift the actor through the faithful conjugation map, normalize one
involution, and use a second independent involution to describe the subgroup.
Small matrix certificates calculate the resulting fixed pairs and their fixer.
The dot-product equivalence connects row-vector fixedness to the actual dual,
and representation operators transport the result back along conjugation.

These are the intrinsic fixed-space inputs to the final paragraph of the proof
of Aschbacher–Smith 15.3.61(2), combined manuscript (1 March 2004), printed p.1151.
The full automorphism normalizer and ambient fusion argument are separate results.
-/

public section
open Matrix BinaryLinearThree Subgroup
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace BinaryLinearThree.FourGroupGeometry.FixedSpaces

private noncomputable abbrev ρ := W.prod W.dual
private abbrev D := BinaryLinearThree.FourGroupGeometry.NaturalDual
private def coordinates : (Vector × Vector) ≃ D :=
  (Equiv.refl Vector).prodCongr (dotProductEquiv (ZMod 2) (Fin 3)).toEquiv
private theorem dual_inverse_fixes (g : Group) (f : Module.Dual (ZMod 2) Vector)
    (h : W.dual g f = f) : W.dual g⁻¹ f = f := by
  have hh := congrArg (W.dual g⁻¹) h
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] at hh
  exact hh.symm
private lemma dual_fixed_iff (g : Group) (d : Vector) :
    W.dual g (dotProductEquiv (ZMod 2) (Fin 3) d) = dotProductEquiv (ZMod 2) (Fin 3) d ↔
      d ᵥ* g.val = d := by
  have hi : W.dual g (dotProductEquiv (ZMod 2) (Fin 3) d) = dotProductEquiv (ZMod 2) (Fin 3) d ↔
      W.dual g⁻¹ (dotProductEquiv (ZMod 2) (Fin 3) d) = dotProductEquiv (ZMod 2) (Fin 3) d :=
    ⟨dual_inverse_fixes g _, fun h => by simpa only [inv_inv] using dual_inverse_fixes g⁻¹ _ h⟩
  rw [hi]
  have he : W.dual g⁻¹ (dotProductEquiv (ZMod 2) (Fin 3) d) =
      dotProductEquiv (ZMod 2) (Fin 3) (d ᵥ* g.val) := by
    apply LinearMap.ext
    intro w
    change d ⬝ᵥ ((g⁻¹)⁻¹.val *ᵥ w) = (d ᵥ* g.val) ⬝ᵥ w
    rw [inv_inv, Matrix.dotProduct_mulVec]
  rw [he]
  exact (dotProductEquiv (ZMod 2) (Fin 3)).injective.eq_iff
private lemma fixes_iff (g : Group) (w : Vector × Vector) :
    fixes g w ↔ ρ g (coordinates w) = coordinates w := by
  change (_ ∧ _) ↔ (W g w.1, W.dual g (dotProductEquiv (ZMod 2) (Fin 3) w.2)) = (w.1, dotProductEquiv (ZMod 2) (Fin 3) w.2)
  rw [Prod.mk.injEq, dual_fixed_iff]
  rfl

private lemma exists_second (H : Subgroup Group) (hc : Nat.card H = 4) (a : H) :
    ∃ b : H, b ≠ 1 ∧ b ≠ a := by
  classical
  let := Fintype.ofFinite H
  have hh : ({1, a} : Finset H).card < (Finset.univ : Finset H).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hc]
    exact (Finset.card_insert_le _ _).trans_lt (by simp)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hh
  exact ⟨b, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb⟩

private lemma four_cover (H : Subgroup Group) (hE : IsElementaryAbelian 2 H)
    (hc : Nat.card H = 4) (a b : H) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    ∀ x : H, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  let := hE
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour H := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  intro x
  by_cases hx : x = 1
  · exact Or.inl hx
  by_cases hxa : x = a
  · exact Or.inr (Or.inl hxa)
  by_cases hxb : x = b
  · exact Or.inr (Or.inr (Or.inl hxb))
  exact Or.inr (Or.inr (Or.inr (IsKleinFour.eq_mul_of_ne_all ha hb hab hx hxa hxb)))


private theorem normalized_fixed (H : Subgroup Group) (hE : IsElementaryAbelian 2 H)
    (hc : Nat.card H = 4) (ht : involution ∈ H) :
    Nat.card (fixedSpace ρ H) = 8 ∧
      ∀ g : Group, (∀ w ∈ fixedSpace ρ H, ρ g w = w) → g ∈ H := by
  let := hE
  let a : H := ⟨involution, ht⟩
  have ha : a ≠ 1 := by
    intro hh
    have : involution = 1 := congrArg Subtype.val hh
    exact (by decide : involution ≠ 1) this
  obtain ⟨b, hb1, hba⟩ := exists_second H hc a
  have hb1' : (b : Group) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbt : (b : Group) ≠ involution := fun h => hba (Subtype.ext h)
  have hsq : (b : Group) * b = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (b : Group) b.property
  have hcomm : (b : Group) * involution = involution * b :=
    congrArg Subtype.val (mul_comm b a)
  have hcover (x : H) : (x : Group) = 1 ∨ (x : Group) = involution ∨
      (x : Group) = b ∨ (x : Group) = involution * b := by
    rcases four_cover H hE hc a b ha hb1 hba.symm x with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  have hf (w : Vector × Vector) :
      coordinates w ∈ fixedSpace ρ H ↔ pairFixed b w := by
    constructor
    · intro hw
      exact ⟨(fixes_iff involution w).mpr (hw a), (fixes_iff b w).mpr (hw b)⟩
    · intro hw x
      change ρ (x : Group) (coordinates w) = coordinates w
      rcases hcover x with h | h | h | h
      · rw [h, map_one, Module.End.one_apply]
      · exact h ▸ (fixes_iff involution w).mp hw.1
      · exact h ▸ (fixes_iff b w).mp hw.2
      · rw [h, map_mul, Module.End.mul_apply, (fixes_iff b w).mp hw.2,
          (fixes_iff involution w).mp hw.1]
  constructor
  · let e : {w : Vector × Vector // pairFixed b w} ≃ fixedSpace ρ H :=
      coordinates.subtypeEquiv (fun w => (hf w).symm)
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
    exact card_pairFixed b hb1' hbt hsq hcomm
  · intro g hg
    have hh : ∀ w : Vector × Vector, pairFixed b w → fixes g w := by
      intro w hw
      exact (fixes_iff g w).mpr (hg (coordinates w) ((hf w).mpr hw))
    rcases mem_four_of_fixes_pairFixed b hb1' hbt hsq hcomm g hh with h | h | h | h
    · exact h ▸ H.one_mem
    · exact h ▸ ht
    · exact h ▸ b.property
    · exact h ▸ H.mul_mem ht b.property

private theorem subgroup_fixed (E : Subgroup Group) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card E = 4) :
    Nat.card (fixedSpace ρ E) = 8 ∧
      ∀ g : Group, (∀ w ∈ fixedSpace ρ E, ρ g w = w) → g ∈ E := by
  let := hE
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : E)
  have ha' : (a : Group) ≠ 1 := fun h => ha (Subtype.ext h)
  have hasq : (a : Group) * a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : Group) a.property
  obtain ⟨k, hk⟩ := exists_involution_conjugator a ha' hasq
  let H := E.map (MulAut.conj k⁻¹).toMonoidHom
  have ht : involution ∈ H := by
    refine ⟨a, a.property, ?_⟩
    change k⁻¹ * a * (k⁻¹)⁻¹ = involution
    rw [inv_inv, mul_assoc, hk, inv_mul_cancel_left]
  have hHE : IsElementaryAbelian 2 H := IsElementaryAbelian.map _
  have hHc : Nat.card H = 4 := (card_map_of_injective (MulAut.conj k⁻¹).injective).trans hc
  obtain ⟨hsize, hfix⟩ := normalized_fixed H hHE hHc ht
  constructor
  · exact (Nat.card_congr (fixedSpaceConjEquiv ρ E k⁻¹).toEquiv).trans hsize
  · intro g hg
    have hh : MulAut.conj k⁻¹ g ∈ H := by
      apply hfix
      intro w hw
      have hwE : ρ k w ∈ fixedSpace ρ E := by
        intro x
        change ρ (x : Group) (ρ k w) = ρ k w
        have hx : MulAut.conj k⁻¹ (x : Group) ∈ H := ⟨x, x.property, rfl⟩
        have he := congrArg (ρ k) (hw ⟨_, hx⟩)
        change ρ k (ρ (k⁻¹ * (x : Group) * (k⁻¹)⁻¹) w) = ρ k w at he
        rw [inv_inv, ← Module.End.mul_apply, ← map_mul] at he
        simpa only [mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] using he
      change ρ (k⁻¹ * g * (k⁻¹)⁻¹) w = w
      rw [inv_inv, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg _ hwE,
        ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    simpa only [MulEquiv.symm_apply_apply] using mem_map_equiv.mp hh

/-- Intrinsic fixed-space geometry of an inner elementary four-group. -/
theorem naturalDualFixed_geometry (A : Subgroup (MulAut Group))
    (hAI : A ≤ MulAut.innerSubgroup Group) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 4) : Nat.card (naturalDualFixed A) = 8 ∧
      ∀ g : Group, (∀ w ∈ naturalDualFixed A, (W g w.1, W.dual g w.2) = w) →
        MulAut.conj g ∈ A := by
  let := hA
  let E := A.comap MulAut.conj
  have hi : Function.Injective (MulAut.conj : Group →* MulAut Group) :=
    MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have hmap : E.map MulAut.conj = A := map_comap_eq_self hAI
  have hEc : Nat.card E = 4 := by
    rw [← card_map_of_injective hi, hmap, hc]
  have hEE : IsElementaryAbelian 2 E := by
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro x y
      apply Subtype.ext
      apply hi
      change MulAut.conj ((x : Group) * y) = MulAut.conj ((y : Group) * x)
      simp only [map_mul]
      exact congrArg Subtype.val (mul_comm (⟨MulAut.conj x, x.property⟩ : A)
        (⟨MulAut.conj y, y.property⟩ : A))
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      apply hi
      change MulAut.conj ((x : Group) ^ 2) = MulAut.conj 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian _ x.property
  exact subgroup_fixed E hEE hEc

end BinaryLinearThree.FourGroupGeometry.FixedSpaces
