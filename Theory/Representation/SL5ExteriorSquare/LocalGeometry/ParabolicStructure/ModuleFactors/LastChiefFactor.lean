module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.ChiefFactors
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.Quotient
public import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The final chief factor of the binary exterior two-space parabolic

The literal quotient V/V₇ is the dual of the natural lower-block SL₃(2)
module. Its complementary-wedge coordinates are 45, 35, 34. The lower-left
zero block removes all other terms from the exterior action, and the resulting
three-by-three minor matrix is the transposed adjugate, hence inverse transpose.
The dot-product equivalence turns these coordinates into the actual linear dual.

The lower-block homomorphism is the second projection of the checked, surjective
Levi homomorphism. Its entry formula identifies it with the literal matrix block.
Pulling back the checked dual-natural irreducibility along this surjection and
transporting through the constructed representation equivalence proves that the
last factor of 0 < V₁ < V₇ < V is irreducible.

Source: Aschbacher–Smith, Lemma 12.5.2(1), printed p.817/PDF p.834.
-/

@[expose] public section
open scoped BigOperators
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
noncomputable section

/-- The actual lower-right block of an SL₅ matrix. -/
def lowerThreeBlock (g : Group) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => g.val i.succ.succ j.succ.succ

/-- The lower SL₃ block of the actual two-space parabolic. -/
def lowerThreeProjection : parabolic 2 →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (MonoidHom.snd _ _).comp (parabolicLeviHom 2 (by decide))

@[simp] theorem lowerThreeProjection_val (g : parabolic 2) :
    (lowerThreeProjection g).val = lowerThreeBlock g.val := by
  ext i j
  change (parabolicLeviHom 2 (by decide) g).2.val i j =
    g.val.val i.succ.succ j.succ.succ
  have hi : (⟨2 + i.val, by omega⟩ : Fin 5) = i.succ.succ := by
    apply Fin.ext
    change 2 + i.val = i.val + 1 + 1
    omega
  have hj : (⟨2 + j.val, by omega⟩ : Fin 5) = j.succ.succ := by
    apply Fin.ext
    change 2 + j.val = j.val + 1 + 1
    omega
  exact (parabolicLeviHom_snd_entry 2 (by decide) g i j).trans
    (congrArg₂ g.val.val hi hj)

theorem lowerThreeProjection_surjective : Function.Surjective lowerThreeProjection := by
  intro a
  obtain ⟨g, hg⟩ := parabolicLeviHom_surjective 2 (by decide) (1, a)
  exact ⟨g, congrArg Prod.snd hg⟩

/-- Complementary-wedge quotient coordinates, in order 45, 35, 34. -/
def lastFactorCoordinates : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := ![coordinates v 9, coordinates v 8, coordinates v 7]
  map_add' v w := by ext i; fin_cases i <;> simp [-coordinates_apply]
  map_smul' c v := by ext i; fin_cases i <;> simp [-coordinates_apply]

theorem lastFactorCoordinates_ker :
    lastFactorCoordinates.ker = seventhSubrepresentation.toSubmodule := by
  ext v
  change lastFactorCoordinates v = 0 ↔ v ∈ V₇
  rw [V₇, mem_coordinateSpan]
  constructor
  · intro h i hi
    have h9 := congrFun h 0
    have h8 := congrFun h 1
    have h7 := congrFun h 2
    fin_cases i <;> simp_all [lastFactorCoordinates, -coordinates_apply]
  · intro h
    ext i
    fin_cases i <;> simp [lastFactorCoordinates, h 9 (by decide), h 8 (by decide),
      h 7 (by decide), -coordinates_apply]

theorem lastFactorCoordinates_surjective : Function.Surjective lastFactorCoordinates := by
  intro w
  refine ⟨coordinates.symm ![0, 0, 0, 0, 0, 0, 0, w 2, w 1, w 0], ?_⟩
  ext i
  fin_cases i <;> simp [lastFactorCoordinates, -coordinates_apply]

/-- The literal quotient V/V₇, identified by its three surviving wedge coordinates. -/
def lastFactorCoordinateEquiv :
    (V ⧸ seventhSubrepresentation.toSubmodule) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ lastFactorCoordinates_ker.symm).trans
    (lastFactorCoordinates.quotKerEquivOfSurjective lastFactorCoordinates_surjective)

@[simp] theorem lastFactorCoordinateEquiv_mk (v : V) :
    lastFactorCoordinateEquiv (seventhSubrepresentation.toSubmodule.mkQ v) =
      lastFactorCoordinates v := rfl

/-- On the three surviving coordinates, the exterior minors are the transposed adjugate. -/
theorem lastFactorCoordinates_action (g : parabolic 2) (v : V) :
    lastFactorCoordinates (exteriorAction 2 g.val v) =
      (lowerThreeBlock g.val).adjugate.transpose.mulVec (lastFactorCoordinates v) := by
  have hz := (mem_parabolic_iff_lowerLeft_zero 2 g.val).mp g.property
  have h20 := hz 2 0 (by decide) (by decide)
  have h21 := hz 2 1 (by decide) (by decide)
  have h30 := hz 3 0 (by decide) (by decide)
  have h31 := hz 3 1 (by decide) (by decide)
  have h40 := hz 4 0 (by decide) (by decide)
  have h41 := hz 4 1 (by decide) (by decide)
  change ![coordinates (exteriorAction 2 g.val v) 9,
    coordinates (exteriorAction 2 g.val v) 8,
    coordinates (exteriorAction 2 g.val v) 7] = _
  rw [coordinates_action, Matrix.adjugate_fin_three]
  ext i
  fin_cases i <;>
    simp [lastFactorCoordinates, lowerThreeBlock, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, actionMatrix, pair, h20, h21, h30, h31, h40, h41,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two, -coordinates_apply] <;> ring

/-- The quotient coordinate action is the inverse transpose of the actual lower block. -/
theorem lastFactorCoordinateEquiv_action (g : parabolic 2)
    (v : V ⧸ seventhSubrepresentation.toSubmodule) :
    lastFactorCoordinateEquiv (lastChiefFactor g v) =
      ((lowerThreeProjection g)⁻¹).val.transpose.mulVec (lastFactorCoordinateEquiv v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change lastFactorCoordinates (exteriorAction 2 g.val v) =
      (lowerThreeProjection g).val.adjugate.transpose.mulVec (lastFactorCoordinates v)
    rw [lowerThreeProjection_val]
    exact lastFactorCoordinates_action g v

/-- The dual-natural module pulled back along the actual lower-block projection. -/
def lastFactorDualNatural :
    Representation (ZMod 2) (parabolic 2) (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :=
  BinaryLinearThree.W.dual.comp lowerThreeProjection

/-- Complementary-wedge coordinates, interpreted as a linear functional by the dot product. -/
def lastFactorDualEquiv :
    (V ⧸ seventhSubrepresentation.toSubmodule) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Fin 3 → ZMod 2) :=
  lastFactorCoordinateEquiv.trans (dotProductEquiv (ZMod 2) (Fin 3))

theorem lastFactorDualEquiv_intertwines (g : parabolic 2)
    (v : V ⧸ seventhSubrepresentation.toSubmodule) :
    lastFactorDualEquiv (lastChiefFactor g v) =
      lastFactorDualNatural g (lastFactorDualEquiv v) := by
  apply LinearMap.ext
  intro w
  change (lastFactorCoordinateEquiv (lastChiefFactor g v)) ⬝ᵥ w =
    lastFactorCoordinateEquiv v ⬝ᵥ ((lowerThreeProjection g)⁻¹).val.mulVec w
  rw [lastFactorCoordinateEquiv_action, Matrix.dotProduct_mulVec]
  exact congrArg (fun d => d ⬝ᵥ w) (Matrix.mulVec_transpose _ _)

/-- An equivalence of the actual quotient representation with the actual pulled-back dual. -/
def lastChiefFactorEquivDualNatural : lastChiefFactor.Equiv lastFactorDualNatural :=
  .mk lastFactorDualEquiv (fun g => by
    apply LinearMap.ext
    intro v
    exact lastFactorDualEquiv_intertwines g v)

theorem lastFactorDualNatural_isIrreducible : IsIrreducible lastFactorDualNatural :=
  (irreducible_comp_surjective_iff lowerThreeProjection lowerThreeProjection_surjective
    BinaryLinearThree.W.dual).mpr BinaryLinearThree.IrreducibleCatalogue.dual_irreducible

/-- The final factor of the source chief chain is irreducible. -/
theorem lastChiefFactor_isIrreducible : IsIrreducible lastChiefFactor :=
  lastChiefFactor_isIrreducible_of_equiv lastChiefFactorEquivDualNatural
    lastFactorDualNatural_isIrreducible

end
end Representation.SL5ExteriorSquare
