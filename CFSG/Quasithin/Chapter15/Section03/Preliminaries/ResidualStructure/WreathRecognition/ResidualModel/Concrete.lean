module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.WreathRecognition.ResidualModel.Actor
public import GorensteinWalter.NormalKleinFourIndexThree

/-!
# The affine model on two independent binary planes

A cubic subgroup of SL₂(2), acting on its natural four-group, gives a
self-centralizing normal Klein four-group of index three. The four-point
recognition theorem therefore identifies its affine group with A₄. The
cubic base acts separately on the two planes, so its affine group is the
product of those two A₄ groups. The isomorphism to the product uses the
literal vector and matrix coordinates throughout.

Source: Aschbacher–Smith, the equivalence in the proof of 15.3.9,
printed p.1123, using the image calculation in 15.3.7.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.WreathRecognition.ResidualModel

attribute [local instance] FourGroupMatrixCoordinates.naturalAction

/-- The restricted natural matrix action on one plane. -/
def planeAction : cubicPlane →* MulAut OrthogonalPlaneVector :=
  letI := FourGroupMatrixCoordinates.naturalAction
  (MulDistribMulAction.toMulAut OrthogonalPlaneActor OrthogonalPlaneVector).comp cubicPlane.subtype

/-- The restricted natural wreath action on both planes. -/
def pairAction : cubicBase →* MulAut OrthogonalVector :=
  letI := orthogonalAction
  (MulDistribMulAction.toMulAut OrthogonalActor OrthogonalVector).comp cubicBase.subtype

/-- The affine group of one plane with its cubic actor. -/
abbrev PlaneAffine := OrthogonalPlaneVector ⋊[planeAction] cubicPlane
/-- The affine group of the rank-four module with its cubic base. -/
abbrev PairAffine := OrthogonalVector ⋊[pairAction] cubicBase

instance planeAffine_finite : Finite PlaneAffine :=
  Finite.of_equiv (OrthogonalPlaneVector × cubicPlane) SemidirectProduct.equivProd.symm

/-- Separate the two affine actions without changing either coordinate. -/
def pairAffineCoordinates : PairAffine ≃* (OrthogonalPlaneIndex → PlaneAffine) where
  toFun x i := ⟨x.left i, baseCoordinates x.right i⟩
  invFun v := ⟨fun i => (v i).left, baseCoordinates.symm (fun i => (v i).right)⟩
  left_inv x := by
    apply SemidirectProduct.ext
    · rfl
    · exact baseCoordinates.symm_apply_apply x.right
  right_inv v := by
    funext i
    apply SemidirectProduct.ext
    · rfl
    · exact congrFun (baseCoordinates.apply_symm_apply (fun i => (v i).right)) i
  map_mul' x y := by
    funext i
    apply SemidirectProduct.ext
    · change x.left i * (x.right.val.left i • y.left (x.right.val.right⁻¹ * i)) =
        x.left i * (x.right.val.left i • y.left i)
      rw [x.right.property.1, inv_one, one_mul]
    · exact congrFun (baseCoordinates.map_mul x.right y.right) i

private theorem planeAffine_model : Nonempty (PlaneAffine ≃* alternatingGroup (Fin 4)) := by
  let := FourGroupMatrixCoordinates.naturalAction_faithful
  let f : PlaneAffine →* cubicPlane := SemidirectProduct.rightHom
  let N := f.ker
  let i : OrthogonalPlaneVector →* PlaneAffine := SemidirectProduct.inl
  have hr : i.range = N := SemidirectProduct.range_inl_eq_ker_rightHom
  let e : OrthogonalPlaneVector ≃* N :=
    (MonoidHom.ofInjective SemidirectProduct.inl_injective).trans (MulEquiv.subgroupCongr hr)
  have hcard : Nat.card N = 4 := by
    rw [← Nat.card_congr e.toEquiv]
    norm_num [OrthogonalPlaneVector, Nat.card_eq_fintype_card]
  have hklein : IsKleinFour N := {
    card_four := hcard
    exponent_two := by
      rw [← Monoid.exponent_eq_of_mulEquiv e, Monoid.exponent_eq_prime_iff Nat.prime_two]
      intro v hv
      exact orderOf_eq_prime (show v ^ 2 = 1 from
        (by decide +kernel : ∀ w : OrthogonalPlaneVector, w ^ 2 = 1) v) hv }
  have hcentral : centralizer (N : Set PlaneAffine) = N := by
    apply le_antisymm
    · intro z hz
      have hfix (v : OrthogonalPlaneVector) : (z.right : OrthogonalPlaneActor) • v = v := by
        have hv : i v ∈ N := hr ▸ (show i v ∈ i.range from ⟨v, rfl⟩)
        have he := congrArg SemidirectProduct.left (hz (i v) hv)
        change v * planeAction 1 z.left = z.left * planeAction z.right v at he
        rw [map_one, MulAut.one_apply] at he
        exact mul_left_cancel ((mul_comm z.left v).trans he).symm
      have hzright : z.right = 1 := by
        apply Subtype.ext
        apply FaithfulSMul.eq_of_smul_eq_smul (α := OrthogonalPlaneVector)
        intro v
        simpa using hfix v
      exact hzright
    · intro z hz w hw
      have hzright : z.right = 1 := hz
      have hwright : w.right = 1 := hw
      apply SemidirectProduct.ext <;> simp [hzright, hwright, mul_comm]
  have hindex : N.index = 3 := by
    rw [show N = f.ker from rfl, index_ker,
      f.range_eq_top_of_surjective SemidirectProduct.rightHom_surjective,
      card_top, cubicPlane_card]
  exact GorensteinWalter.mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    N inferInstance hklein hcentral hindex

private def twoCoordinates (A : Type*) [Group A] :
    (OrthogonalPlaneIndex → A) ≃* (A × A) where
  toFun f := (f (Multiplicative.ofAdd 0), f (Multiplicative.ofAdd 1))
  invFun p i := if i = Multiplicative.ofAdd 0 then p.1 else p.2
  left_inv f := by
    funext i
    have hi : i = Multiplicative.ofAdd 0 ∨ i = Multiplicative.ofAdd 1 := by
      change i.toAdd = 0 ∨ i.toAdd = 1
      exact (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) i.toAdd
    rcases hi with rfl | rfl <;> simp
  right_inv _ := by simp
  map_mul' _ _ := rfl

/-- The literal cubic affine group is a pair of alternating four-groups. -/
theorem pairAffine_model :
    Nonempty (PairAffine ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  obtain ⟨e⟩ := planeAffine_model
  exact ⟨pairAffineCoordinates.trans ((MulEquiv.piCongrRight (fun _ => e)).trans
    (twoCoordinates _))⟩

end CFSG.Quasithin.Chapter15.Section03.WreathRecognition.ResidualModel

end
