module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
public import Theory.Representation.DegreeFourFrattini
public import Theory.GroupTheory.SylowFrattiniBounds

/-!
# Small Sylow Frattini quotients in odd-prime G₂

The constructed orthogonal subgroup of odd index preserves the two quaternion
summands of the split octonions. Its action on the second summand is faithful:
products of two vectors there span the first summand. The degree-four bound
therefore gives at most seven Frattini generators for its Sylow two-subgroups.
Odd index and Sylow conjugacy transfer the bound to the full octonion model.
The prime-three endpoint follows directly from the exact group order.

This is the model input for the original A₅ pair's Sylow restriction in
Aschbacher–Smith, 4.4.10, printed p.621. The coordinate construction retains
the licensed ATLAS realization imported below; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Atlas.G2.OddSylowFrattini
open Atlas.SplitOctonion
open MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
open MultiplierOrdinary.OddTwoPrimary
open MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
variable {F : Type*} [Field F]

private def pairAction (g : Model F) : (Mat F × Mat F) ≃ₗ[F] (Mat F × Mat F) :=
  coordinates.symm.trans (g.val.trans coordinates)

private theorem pairAction_mul (g h : Model F) (x : Mat F × Mat F) :
    pairAction (g*h) x = pairAction g (pairAction h x) := by
  simp [pairAction]

private theorem pairAction_preserves (g : Model F) (x y : Mat F × Mat F) :
    pairAction g (pairMul x y) = pairMul (pairAction g x) (pairAction g y) := by
  have hc (z w : Mat F × Mat F) :
      coordinates.symm (pairMul z w) = mul (coordinates.symm z) (coordinates.symm w) := by
    apply coordinates.injective
    simp [coordinates_mul]
  simp only [pairAction, LinearEquiv.trans_apply, hc, automorphism_mul, coordinates_mul]

private theorem image_preserves_second (d : F) (hd : d ≠ 0)
    (g : (inclusion d hd).range) (b : Mat F) :
    (pairAction g.val (0,b)).1 = 0 := by
  obtain ⟨x,hx⟩ := g.property
  rw [← hx]
  have hc : x.right = 1 ∨ x.right = .ofAdd 1 := by
    have hi : x.right.toAdd.val < 2 := x.right.toAdd.val_lt
    have hh : x.right.toAdd.val = 0 ∨ x.right.toAdd.val = 1 := by omega
    rcases hh with hh | hh
    · left; apply Equiv.injective Multiplicative.toAdd; exact (ZMod.val_injective 2 hh)
    · right; apply Equiv.injective Multiplicative.toAdd; exact (ZMod.val_injective 2 hh)
  rcases hc with hc | hc
  · simp [pairAction, OrthogonalMap.inclusion, SemidirectProduct.lift, hc, productHom,
      octonionEquiv, pairEquiv, pairLinear]
  · simp [pairAction, OrthogonalMap.inclusion, SemidirectProduct.lift, hc, productHom,
      octonionEquiv, pairEquiv, pairLinear, outerHom, involutionHom_generator,
      outer, outerEquiv, pairTwist, twist]
    have hz : (!![0,0;0,0] : Mat F) = 0 := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hz, mul_zero, zero_mul]

private def secondAction (d : F) (hd : d ≠ 0) :
    Representation F (inclusion d hd).range (Mat F) where
  toFun g := (LinearMap.snd F (Mat F) (Mat F)).comp
    ((pairAction g.val).toLinearMap.comp (LinearMap.inr F (Mat F) (Mat F)))
  map_one' := by
    apply LinearMap.ext
    intro b
    change (pairAction 1 (0,b)).2 = b
    simp [pairAction]
  map_mul' g h := by
    apply LinearMap.ext
    intro b
    change (pairAction (g.val*h.val) (0,b)).2 =
      (pairAction g.val (0, (pairAction h.val (0,b)).2)).2
    rw [pairAction_mul]
    congr 2
    exact Prod.ext (image_preserves_second d hd h b) rfl

private theorem pairAction_second (d : F) (hd : d ≠ 0)
    (g : (inclusion d hd).range) (b : Mat F) :
    pairAction g.val (0,b) = (0,secondAction d hd g b) := by
  exact Prod.ext (image_preserves_second d hd g b) rfl

private theorem secondAction_injective (d : F) (hd : d ≠ 0) :
    Function.Injective (secondAction d hd) := by
  intro g h he
  have hs (b : Mat F) : pairAction g.val (0,b) = pairAction h.val (0,b) := by
    rw [pairAction_second, pairAction_second, he]
  have hf (a : Mat F) : pairAction g.val (a,0) = pairAction h.val (a,0) := by
    have hm : pairMul ((0,-a) : Mat F × Mat F) (0,1) = (a,0) := by
      have hz : bar (0 : Mat F) = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [bar]
      simp [pairMul, bar_one, hz]
    rw [← hm, pairAction_preserves, pairAction_preserves, hs, hs]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply coordinates.injective
  have heq : coordinates (g.val.val x) = pairAction g.val (coordinates x) := by simp [pairAction]
  have heq' : coordinates (h.val.val x) = pairAction h.val (coordinates x) := by simp [pairAction]
  rw [heq, heq']
  obtain ⟨a,b⟩ := coordinates x
  have hab : (a,b) = (a,0) + (0,b) := by simp
  rw [hab, map_add, map_add, hs, hf]

private theorem prime_frattini_card_le {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (P : Sylow 2 (Model (ZMod p))) : Nat.card (P ⧸ frattini P) ≤ 128 := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  let d := -a
  have hd : d ≠ 0 := neg_ne_zero.mpr ha0
  let H := (OrthogonalMap.inclusion d hd).range
  have hindex : ¬ 2 ∣ H.index := by
    rw [← even_iff_two_dvd]
    exact (Nat.not_even_iff_odd.mpr (odd_index_of_diagonal_kernel
      (F := ZMod p) (by simp [Nat.card_eq_fintype_card]) hp
      (action d hd) (OrthogonalMap.inclusion d hd)
      (inclusion_kernel d hd (by simpa [d] using ha))))
  let Q : Sylow 2 H := Classical.choice inferInstance
  have hm : ¬ 2 ∣ ((Q : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two Q.not_dvd_index hindex
  let S : Sylow 2 (Model (ZMod p)) := (Q.isPGroup'.map H.subtype).toSylow hm
  have he : Q ≃* S := Q.equivMapOfInjective H.subtype H.subtype_injective
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  have hQ : Nat.card (Q ⧸ frattini Q) ≤ 128 :=
    Representation.card_frattini_quotient_le_128_of_faithful_degree_four
      Q.isPGroup' ((secondAction d hd).comp (Q : Subgroup H).subtype)
      ((secondAction_injective d hd).comp (Q : Subgroup H).subtype_injective) h2
      (by simp [Mat, Module.finrank_matrix])
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (Sylow.equiv P S),
    ← Theory.GroupTheory.SylowFrattiniBounds.card_congr he]
  exact hQ

/-- Every odd-prime G₂ Sylow two-subgroup has at most seven Frattini generators. -/
theorem frattini_card_le [Finite F] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hF : Nat.card F = p) (P : Sylow 2 (Model F)) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  by_cases h3 : p = 3
  · apply Theory.GroupTheory.SylowFrattiniBounds.card_le_of_order_not_dvd (n := 7) P
    norm_num [Atlas.G2.card_Model, hF, h3]
  · have hp3 : 3 < p := by
      have hprime := (Fact.out : p.Prime).two_le
      have hne : p ≠ 2 := by rintro rfl; norm_num at hp
      omega
    let := Fintype.ofFinite F
    let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F Fact.out
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let f := fieldEquiv e.symm
    let Q := P.mapSurjective (f := f.toMonoidHom) f.surjective
    have he : P ≃* Q := P.equivMapOfInjective f.toMonoidHom f.injective
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr he]
    exact prime_frattini_card_le hp3 Q

end Atlas.G2.OddSylowFrattini
