module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Setup
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs

/-!
# The marked four-dimensional end-node Levi quotient

The ordered diagonal-block quotient identifies the relative two-core kernel.
All factors except the four-dimensional block are trivial over F₂. Keeping
that block's original coordinate order gives the actual SL₄ quotient, with
its matrix entries recorded on parabolic representatives.

Source: Guralnick–Malle, Classification of 2F-modules II, Theorem 3.1 and
Proposition 4.7(2); Aschbacher–Smith K.3.2, printed pp.454–455.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes

namespace Levi

def label (e : Fin 2) (i : Fin 5) : Fin 5 := if i.val ≤ (node e).val then 0 else 1

def largeBlock (e : Fin 2) : Fin 5 := if e = 0 then 1 else 0

def includedCoordinate (e : Fin 2) (i : Fin 4) : Fin 5 :=
  if e = 0 then i.succ else i.castSucc

theorem label_monotone (e : Fin 2) : Monotone (label e) := by
  revert e
  decide

theorem label_lt_iff (e : Fin 2) (i j : Fin 5) :
    label e j < label e i ↔ (node e).val < i.val ∧ j.val ≤ (node e).val := by
  revert e i j
  decide

/-- The marked matrix parabolic and the literal ordered-block linear group. -/
noncomputable def parabolicEquiv (e : Fin 2) : parabolic e ≃* triangularGroup (label e) where
  toFun g := ⟨slEquivLinear 5 g, by
    intro i j hij
    have h := (label_lt_iff e i j).mp hij
    simpa only [matrix, MulEquiv.symm_apply_apply] using
      (mem_parabolic_iff e g).mp g.property i j h.1 h.2⟩
  invFun g := ⟨(slEquivLinear 5).symm g, by
    apply (mem_parabolic_iff e _).mpr
    intro i j hi hj
    exact g.property ((label_lt_iff e i j).mpr ⟨hi, hj⟩)⟩
  left_inv g := Subtype.ext ((slEquivLinear 5).symm_apply_apply g)
  right_inv g := Subtype.ext ((slEquivLinear 5).apply_symm_apply g)
  map_mul' _ _ := Subtype.ext (map_mul (slEquivLinear 5) _ _)

@[simp] theorem parabolicEquiv_coe (e : Fin 2) (g : parabolic e) :
    (parabolicEquiv e g).val = slEquivLinear 5 g.val := rfl

/-- Ordered coordinates of the only nontrivial diagonal block. -/
def indexEquiv (e : Fin 2) : Fin 4 ≃ Block (label e) (largeBlock e) where
  toFun i := ⟨includedCoordinate e i, by revert e i; decide⟩
  invFun i := if h : e = 0 then ⟨i.val.val - 1, by
    have hi := i.val.isLt
    omega⟩ else ⟨i.val.val, by
    have hm := i.property
    have he : e = 1 := by omega
    simp [label, node, largeBlock, he] at hm
    omega⟩
  left_inv i := by
    apply Fin.ext
    fin_cases e <;> simp [includedCoordinate]
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    fin_cases e
    · have hm := i.property
      simp [label, node, largeBlock] at hm
      simp [includedCoordinate]
      omega
    · simp [includedCoordinate]

noncomputable def coordinates (e : Fin 2) :
    BlockSpace (label e) (largeBlock e) ≃ₗ[ZMod 2] Space 4 :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (indexEquiv e)

theorem otherBlock_card (e : Fin 2) (k : Fin 5) (hk : k ≠ largeBlock e) :
    Fintype.card (Block (label e) k) ≤ 1 := by
  revert e k
  decide

theorem projection_bijective (e : Fin 2) :
    Function.Bijective (Pi.evalMonoidHom
      (fun k => BinaryLinear.GL (BlockSpace (label e) k)) (largeBlock e)) := by
  constructor
  · intro a b hab
    funext k
    by_cases hk : k = largeBlock e
    · subst k; exact hab
    exact (linearBlock_eq_one_of_card_le_one _ _ (otherBlock_card e k hk) (a k)).trans
      (linearBlock_eq_one_of_card_le_one _ _ (otherBlock_card e k hk) (b k)).symm
  · intro a
    exact ⟨Function.update 1 (largeBlock e) a, Function.update_self ..⟩

/-- The actual relative two-core quotient, in the original tail or head coordinates. -/
noncomputable def quotientEquiv (e : Fin 2) :
    (parabolic e ⧸ radical e) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  (QuotientGroup.congr _ _ (parabolicEquiv e) (pCore_map_iso 2 (parabolicEquiv e))).trans
    ((diagonalQuotientEquiv (label e) (label_monotone e)).trans
      ((MulEquiv.ofBijective
        (Pi.evalMonoidHom (fun k => BinaryLinear.GL (BlockSpace (label e) k)) (largeBlock e))
        (projection_bijective e)).trans
        ((linearGroupCongr (coordinates e)).trans (slEquivLinear 4).symm)))

/-- On representatives the quotient is the literal four-by-four diagonal submatrix. -/
theorem quotientEquiv_mk_val (e : Fin 2) (g : parabolic e) (i j : Fin 4) :
    (quotientEquiv e (QuotientGroup.mk' (radical e) g)).val i j =
      g.val.val (includedCoordinate e i) (includedCoordinate e j) := by
  let f := diagonalFactor (label e) (largeBlock e) (parabolicEquiv e g)
  have he : slEquivLinear 4 (quotientEquiv e (QuotientGroup.mk' (radical e) g)) =
      linearGroupCongr (coordinates e) f := (slEquivLinear 4).apply_symm_apply _
  have h := congrArg (fun a : LinearGroup 4 => a (Pi.single j 1) i) he
  rw [slEquivLinear_apply, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h]
  change (∑ k : Block (label e) (largeBlock e),
    matrix ((parabolicEquiv e g).val) (indexEquiv e i).val k.val *
      (coordinates e).symm (Pi.single j 1) k) = _
  rw [← (indexEquiv e).sum_comp]
  simp only [parabolicEquiv_coe, matrix, MulEquiv.symm_apply_apply]
  change (∑ k : Fin 4,
    g.val.val (includedCoordinate e i) (includedCoordinate e k) *
      ((coordinates e) ((coordinates e).symm (Pi.single j 1))) k) = _
  rw [LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

/-- The original four-space action of the quotient on the radical fixed vectors. -/
noncomputable abbrev action {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (e : Fin 2) :=
  (quotientRepresentation σ e).comp (quotientEquiv e).symm.toMonoidHom

@[simp] theorem action_quotientEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (e : Fin 2)
    (g : parabolic e ⧸ radical e) :
    action σ e (quotientEquiv e g) = quotientRepresentation σ e g := by
  change quotientRepresentation σ e ((quotientEquiv e).symm (quotientEquiv e g)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The coordinate inclusion is injective. -/
theorem includedCoordinate_injective (e : Fin 2) : Function.Injective (includedCoordinate e) :=
  fun _ _ h => (indexEquiv e).injective (Subtype.ext h)

/-- Every elementary matrix in the four-block is an actual parabolic element. -/
def root (e : Fin 2) (i j : Fin 4) (hij : i ≠ j) (c : ZMod 2) : parabolic e :=
  ⟨Matrix.SpecialLinearGroup.transvection
    (fun h => hij (includedCoordinate_injective e h)) c, by
    apply (mem_parabolic_iff e _).mpr
    intro r s hr hs
    have he (a : Fin 4) : label e (includedCoordinate e a) = largeBlock e :=
      (indexEquiv e a).property
    exact Matrix.blockTriangular_transvection (b := label e)
      (by rw [he, he]) c ((label_lt_iff e r s).mpr ⟨hr, hs⟩)⟩

/-- The literal root matrix descends to the same root matrix in SL₄. -/
theorem quotientEquiv_root (e : Fin 2) (i j : Fin 4) (hij : i ≠ j) (c : ZMod 2) :
    quotientEquiv e (QuotientGroup.mk' (radical e) (root e i j hij c)) =
      Matrix.SpecialLinearGroup.transvection hij c := by
  apply Subtype.ext
  ext a b
  rw [quotientEquiv_mk_val]
  change (Matrix.SpecialLinearGroup.transvection
    (fun h => hij (includedCoordinate_injective e h)) c).val
      (includedCoordinate e a) (includedCoordinate e b) = _
  simp [Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply, Matrix.single, (includedCoordinate_injective e).eq_iff]

/-- Passing to the quotient and pulling back along its marking preserves root operators. -/
theorem action_root {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (e : Fin 2) (i j : Fin 4) (hij : i ≠ j) (c : ZMod 2) (v : FixedSpace σ e) :
    (action σ e (Matrix.SpecialLinearGroup.transvection hij c) v : V) =
      σ (root e i j hij c).val v := by
  rw [← quotientEquiv_root e i j hij c, action_quotientEquiv]
  rfl

end Levi
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
