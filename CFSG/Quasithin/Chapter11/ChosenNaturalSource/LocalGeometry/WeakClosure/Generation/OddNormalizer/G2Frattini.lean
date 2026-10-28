module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SpecialFourFrattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OddG2
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
public import Theory.Representation.DegreeFourFrattini
public import Theory.GroupTheory.SylowFrattiniBounds

/-!
# Small Sylow Frattini quotients in odd-prime G₂

The constructed orthogonal subgroup of odd index preserves the two quaternion
summands of the split octonions. Its action on the second summand is faithful:
products of two vectors there span the first summand. The degree-four bound
together with the model’s two-rank bound therefore gives at most five
Frattini generators for its Sylow two-subgroups.
Odd index and Sylow conjugacy transfer the bound to the full octonion model.
At prime three, the same orthogonal subgroup has order 576 and odd index
7371, proved from the exact kernel and group orders.

This supplies the odd-prime G₂ outer-section exclusion in the original
4.4.10–11 argument, Aschbacher–Smith, printed pp.621–623. The local second
summand action follows Theory/SpecificGroups/G2/OddSylowFrattini.lean, and
the coordinate construction retains
the licensed ATLAS realization imported below; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.G2Frattini
open Atlas.G2
open Atlas.SplitOctonion
open MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
open MultiplierOrdinary.OddTwoPrimary
open MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
variable {F : Type*} [Field F]

private def pairAction (g : Model F) : (Mat F × Mat F) ≃ₗ[F] (Mat F × Mat F) :=
  Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates.symm.trans (g.val.trans Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates)

private theorem pairAction_mul (g h : Model F) (x : Mat F × Mat F) :
    pairAction (g*h) x = pairAction g (pairAction h x) := by
  simp [pairAction]

private theorem pairAction_preserves (g : Model F) (x y : Mat F × Mat F) :
    pairAction g (pairMul x y) = pairMul (pairAction g x) (pairAction g y) := by
  have hc (z w : Mat F × Mat F) :
      Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates.symm (pairMul z w) = mul (Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates.symm z) (Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates.symm w) := by
    apply Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates.injective
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
  apply Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates.injective
  have heq : Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates (g.val.val x) = pairAction g.val (Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates x) := by simp [pairAction]
  have heq' : Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates (h.val.val x) = pairAction h.val (Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates x) := by simp [pairAction]
  rw [heq, heq']
  obtain ⟨a,b⟩ := Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne.coordinates x
  have hab : (a,b) = (a,0) + (0,b) := by simp
  rw [hab, map_add, map_add, hs, hf]

/-- Every Sylow two-subgroup of the actual odd-prime octonion model has
Frattini quotient of order at most 32. -/
theorem prime_frattini_card_le {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (P : Sylow 2 (Model (ZMod p))) : Nat.card (P ⧸ frattini P) ≤ 32 := by
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
    apply Nat.not_even_iff_odd.mpr
    by_cases hp3 : 3 < p
    · exact odd_index_of_diagonal_kernel
        (F := ZMod p) (by simp [Nat.card_eq_fintype_card]) hp3
        (action d hd) (OrthogonalMap.inclusion d hd)
        (inclusion_kernel d hd (by simpa [d] using ha))
    · have he : p = 3 := by omega
      subst p
      let j := OrthogonalMap.inclusion d hd
      let z : (RankOne 3 × RankOne 3) ⋊[action d hd] C2 := SemidirectProduct.inl (-1,-1)
      have hz : z ≠ 1 := by
        intro h
        have h' := congrArg (fun x : (RankOne 3 × RankOne 3) ⋊[action d hd] C2 => x.left.1.val 0 0) h
        change (-1 : ZMod 3) = 1 at h'
        have hz : (2 : ZMod 3) = 0 := by linear_combination -h'
        have hh := (ZMod.natCast_eq_zero_iff 2 3).mp hz
        norm_num at hh
      have hk : Nat.card j.ker = 2 := by
        apply (Nat.card_eq_two_iff' (1 : j.ker)).mpr
        have hj := inclusion_kernel d hd (by simpa [d] using ha)
        refine ⟨⟨z,(hj z).mpr (Or.inr rfl)⟩,fun h => hz (congrArg Subtype.val h),?_⟩
        intro x hx
        rcases (hj x).mp x.property with h | h
        · exact (hx (Subtype.ext h)).elim
        · exact Subtype.ext h
      have hdom : Nat.card ((RankOne 3 × RankOne 3) ⋊[action d hd] C2) = 1152 := by
        rw [SemidirectProduct.card,Nat.card_prod,Atlas.card_sl_two]
        norm_num [C2,Nat.card_eq_fintype_card]
      have hr : Nat.card H = 576 := by
        have h := j.ker.card_mul_index
        rw [index_ker,hk,hdom] at h
        change 2 * Nat.card H = 1152 at h
        omega
      have hidx := H.card_mul_index
      rw [hr,Atlas.G2.card_Model] at hidx
      norm_num [Nat.card_eq_fintype_card] at hidx
      have hh : H.index = 7371 := by omega
      rw [hh]
      decide
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
  have hQ : Nat.card (Q ⧸ frattini Q) ≤ 32 :=
    CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SpecialFourFrattini.degree_four_frattini_le_thirtytwo_of_twoRank_le_three
      Q.isPGroup' ((secondAction d hd).comp (Q : Subgroup H).subtype)
      ((secondAction_injective d hd).comp (Q : Subgroup H).subtype_injective) h2
      (by simp [Mat, Module.finrank_matrix]) (by
        have hr := CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.odd_g2_twoRank_le_three
          ((Fact.out : p.Prime).odd_of_ne_two (by omega))
          (Q := Model (ZMod p))
          ⟨ZMod p,inferInstance,inferInstance,by simp [Nat.card_eq_fintype_card],⟨MulEquiv.refl _⟩⟩
        exact (primeRank_le_of_injective 2
          (H.subtype.comp (Q : Subgroup H).subtype)
          (H.subtype_injective.comp (Q : Subgroup H).subtype_injective)).trans hr)
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (Sylow.equiv P S),
    ← Theory.GroupTheory.SylowFrattiniBounds.card_congr he]
  exact hQ


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.G2Frattini
