module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.RootEntries.Transport

/-!
# Fixed root coordinates orthogonal to E6

All E7 and E8 roots have squared length two. If a root is orthogonal to a
selected simple root, neither its sum nor its difference with that simple
root is a root. Its row in both signed first operators therefore vanishes.
The quadratic-curve and evaluated-word arguments in `FixedRows` give the
literal identity row for every word. No centrality or diagonality is needed.
In particular this normalizes the trivial root constituents in E8, including
in characteristic three.

Sources: GLS3 §2.6.2 (closed subsystems on the common Chevalley lattice),
used in §§1.12.5–6 and Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section

noncomputable section
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
attribute [local instance] Classical.decEq

private theorem norm_two_orthogonal_no_add (r i s : Vec 8)
    (hr : dot r r = 2) (hi : dot i i = 2) (hs : dot s s = 2)
    (hri : dot r i = 0) : r ≠ i + s := by
  intro h
  have he : s = r - i := by rw [h]; abel
  have hd : dot (r - i) (r - i) = dot r r - 2 * dot r i + dot i i := by
    simp only [dot, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hs
  linarith

private theorem norm_two_orthogonal_no_sub (r i s : Vec 8)
    (hr : dot r r = 2) (hi : dot i i = 2) (hs : dot s s = 2)
    (hri : dot r i = 0) : r ≠ s - i := by
  intro h
  have he : s = r + i := by rw [h]; abel
  have hd : dot (r + i) (r + i) = dot r r + 2 * dot r i + dot i i := by
    simp only [dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hs
  linarith

section Generic
variable {ι R M N F : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι] [Field F]

private theorem isolated_simpleCoefficient_row (i : b.support) (r : ι)
    (hp : r ≠ (i : ι)) (hm : r ≠ P.reflectionPerm i i)
    (ha : ∀ s, P.root r ≠ P.root i + P.root s)
    (hs : ∀ s, P.root r ≠ P.root s - P.root i)
    (sign : Bool) (c : b.support ⊕ ι) :
    (simpleFamily (b := b)).coefficient (S := F) (sign, i) 1 (Sum.inr r) c = 0 := by
  cases sign <;> cases c <;>
    simp [IntegralCubicFamily.coefficient, simpleFamily, eDividedPower_one,
      fDividedPower_one, eMatrix, fMatrix, hp, hm, ha, hs]

end Generic

local instance constancyFixedRootsE7Fintype : Fintype typeE7Roots := Fintype.ofFinite _
local instance constancyFixedRootsE8Fintype : Fintype typeE8Roots := Fintype.ofFinite _

private theorem e8_orthogonal_row {F : Type*} [Field F]
    (i : typeE8RootPairing_base.support) (r : typeE8Roots)
    (hr : typeE8RootPairing.pairing r i = 0) (s : Bool)
    (c : typeE8RootPairing_base.support ⊕ typeE8Roots) :
    (simpleFamily (b := typeE8RootPairing_base)).coefficient (S := F)
      (s, i) 1 (Sum.inr r) c = 0 := by
  apply isolated_simpleCoefficient_row i r
  · intro h
    subst r
    simp at hr
  · intro h
    rw [h] at hr
    simp at hr
  · intro t h
    exact norm_two_orthogonal_no_add r.val (i : typeE8Roots).val t.val
      (typeE8Root_dot_self r) (typeE8Root_dot_self i) (typeE8Root_dot_self t)
      (by simpa only [typeE8RootPairing_pairing] using hr) h
  · intro t h
    exact norm_two_orthogonal_no_sub r.val (i : typeE8Roots).val t.val
      (typeE8Root_dot_self r) (typeE8Root_dot_self i) (typeE8Root_dot_self t)
      (by simpa only [typeE8RootPairing_pairing] using hr) h

private theorem e7_orthogonal_row {F : Type*} [Field F]
    (i : typeE7RootPairing_base.support) (r : typeE7Roots)
    (hr : typeE7RootPairing.pairing r i = 0) (s : Bool)
    (c : typeE7RootPairing_base.support ⊕ typeE7Roots) :
    (simpleFamily (b := typeE7RootPairing_base)).coefficient (S := F)
      (s, i) 1 (Sum.inr r) c = 0 := by
  apply isolated_simpleCoefficient_row i r
  · intro h
    subst r
    simp at hr
  · intro h
    rw [h] at hr
    simp at hr
  · intro t h
    exact norm_two_orthogonal_no_add r.val (i : typeE7Roots).val t.val
      (typeE7Root_dot_self r) (typeE7Root_dot_self i) (typeE7Root_dot_self t)
      hr (congrArg Subtype.val h)
  · intro t h
    exact norm_two_orthogonal_no_sub r.val (i : typeE7Roots).val t.val
      (typeE7Root_dot_self r) (typeE7Root_dot_self i) (typeE7Root_dot_self t)
      hr (congrArg Subtype.val h)

private theorem odd_two_ne_zero {F : Type*} [Field F]
    (hodd : Odd (ringChar F)) : (2 : F) ≠ 0 := by
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h) with h | h
  · exact CharP.ringChar_ne_one (R := F) h
  · exact hodd.not_two_dvd_nat (by rw [h])

/-- A root orthogonal to the selected E6 roots has a fixed coordinate row in E8. -/
theorem e8Six_orthogonal_root_row (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F) (r : typeE8Roots)
    (hr : ∀ i, typeE8RootPairing.pairing r (e8Node i) = 0)
    (c : typeE8RootPairing_base.support ⊕ typeE8Roots) :
    (e8Six F w).val.val (Sum.inr r) c =
      (1 : Matrix (typeE8RootPairing_base.support ⊕ typeE8Roots)
        (typeE8RootPairing_base.support ⊕ typeE8Roots) F) (Sum.inr r) c := by
  apply eval_fixed_row ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F))
  intro s i t c
  change (e8Six F (FreeGroup.of (s, i, t))).val.val _ c = _
  simp only [e8Six_of, e8Simple, signedSimple_val, IntegralCubicFamily.unit_val]
  apply curve_fixed_row _ _ (e8_simple_third_zero s _) _ (odd_two_ne_zero hodd)
  exact fun c => e8_orthogonal_row _ _ (hr i) s c

/-- A root orthogonal to the selected E6 roots has a fixed coordinate row in E7. -/
theorem e7Six_orthogonal_root_row (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F) (r : typeE7Roots)
    (hr : ∀ i, typeE7RootPairing.pairing r (e7Node i) = 0)
    (c : typeE7RootPairing_base.support ⊕ typeE7Roots) :
    (e7Six F w).val.val (Sum.inr r) c =
      (1 : Matrix (typeE7RootPairing_base.support ⊕ typeE7Roots)
        (typeE7RootPairing_base.support ⊕ typeE7Roots) F) (Sum.inr r) c := by
  apply eval_fixed_row ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F))
  intro s i t c
  change (e7Six F (FreeGroup.of (s, i, t))).val.val _ c = _
  simp only [e7Six_of, e7Simple, signedSimple_val, IntegralCubicFamily.unit_val]
  apply curve_fixed_row _ _ (e7_simple_third_zero s _) _ (odd_two_ne_zero hodd)
  exact fun c => e7_orthogonal_row _ _ (hr i) s c

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
