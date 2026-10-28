module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreSeedAction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.BinaryPlaneLifts
public import Theory.LinearAlgebra.ZModFourPlaneCorrection

/-!
# Binary reductions of the actual HS plane lifts

The binary plane shears are constructed on the original seed in coordinates
induced from the entire cyclic-four core. Evaluating the actual matrix action
on the three doubled basis vectors therefore gives the required reductions
over F₂. No matrix normal form is a source hypothesis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
open BinaryPlane
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem doubled_basis (j : Fin 3) :
    (fun i => binaryDouble ((Pi.single j 1 : Fin 3 → ZMod 2) i)) = Pi.single j 2 := by
  revert j
  decide +kernel

/-- The first actual plane lift has the first standard shear as its binary
reduction, in the same whole-core coordinates used to construct the seed. -/
theorem TypeAt.first_plane_matrix_reduction (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (a : normalizer (V : Set G))
    (ha : V.normalizerMonoidHom a = alphaAt (h.seedCoordinates e)) :
    (h.coreMatrixAction e a).map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  apply ZModFourPlaneCorrection.reduction_eq_of_doubled_basis
  intro j
  have hh := h.coreMatrixAction_on_seed e a (Multiplicative.ofAdd (Pi.single j 1))
  rw [ha] at hh
  simp only [alphaAt_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, doubled_basis] at hh
  exact hh.trans ((by decide +kernel : ∀ j : Fin 3,
    (fun i => binaryDouble ((alpha (Multiplicative.ofAdd (Pi.single j 1))).toAdd i)) =
      fun i => 2 * (((!![1, 0, 1; 0, 1, 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) i j).val : ZMod 4)) j)

/-- The second actual plane lift has the second standard shear as its binary
reduction in those same original-core coordinates. -/
theorem TypeAt.second_plane_matrix_reduction (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (b : normalizer (V : Set G))
    (hb : V.normalizerMonoidHom b = betaAt (h.seedCoordinates e)) :
    (h.coreMatrixAction e b).map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] := by
  apply ZModFourPlaneCorrection.reduction_eq_of_doubled_basis
  intro j
  have hh := h.coreMatrixAction_on_seed e b (Multiplicative.ofAdd (Pi.single j 1))
  rw [hb] at hh
  simp only [betaAt_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, doubled_basis] at hh
  exact hh.trans ((by decide +kernel : ∀ j : Fin 3,
    (fun i => binaryDouble ((beta (Multiplicative.ofAdd (Pi.single j 1))).toAdd i)) =
      fun i => 2 * (((!![1, 0, 0; 0, 1, 1; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) i j).val : ZMod 4)) j)

end CFSG.Quasithin.HigmanSims
