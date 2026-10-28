module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SmallModels.Cubic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SmallModels.SymmetricThree
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.Representation.SpecialLinearNatural

/-!
# Action-compatible matrix and projective coordinates

The canonical SL₃(2)–GL₃(2) and SL₃(2)–PSL₃(2) equivalences intertwine the
actual natural actions. Thus the cubic calculations apply to these concrete
group models and to two identical copies. The odd-degree core equivalence
likewise reconciles the two natural-module conventions for S₃.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.67,
printed p.1154, with the module conventions of B.3 and B.5.1, printed pp.82–85, 99.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
open BestReduction
namespace LinearThree
noncomputable def matrixEquiv : Matrix.PSL3Two.SL ≃* Actor :=
  Matrix.PSL3Two.equivGL.trans (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space))

theorem matrixEquiv_natural (g : Matrix.PSL3Two.SL) (v : Space) :
    natural (matrixEquiv g) v = specialLinearNatural 3 g v := by
  simp only [matrixEquiv, MulEquiv.trans_apply, Matrix.PSL3Two.equivGL_apply]
  rfl

noncomputable def projectiveEquiv : Matrix.PSL3Two.PSL ≃* Actor :=
  Matrix.PSL3Two.equiv.symm.trans matrixEquiv

/-- The actual projective natural action, through the inverse of the canonical
SL₃(2) to PSL₃(2) projection. -/
noncomputable def projectiveNatural : Representation (ZMod 2) Matrix.PSL3Two.PSL Space :=
  (specialLinearNatural 3).comp Matrix.PSL3Two.equiv.symm.toMonoidHom

theorem projectiveEquiv_natural (g : Matrix.PSL3Two.PSL) (v : Space) :
    natural (projectiveEquiv g) v = projectiveNatural g v :=
  matrixEquiv_natural _ _
end LinearThree

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]

theorem matrixThree_marked_cubic
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ (specialLinearNatural (k := ZMod 2) 3)) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v := by
  apply linearThree_marked_cubic d
  exact { actor := c.actor.trans LinearThree.matrixEquiv
          coordinates := c.coordinates
          intertwines := fun g v => (c.intertwines g v).trans
            (LinearThree.matrixEquiv_natural _ _).symm }

theorem doubleMatrixThree_marked_cubic
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ
      ((specialLinearNatural (k := ZMod 2) 3).prod (specialLinearNatural 3))) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v := by
  apply doubleLinearThree_marked_cubic d
  refine { actor := c.actor.trans LinearThree.matrixEquiv
           coordinates := c.coordinates
           intertwines := ?_ }
  intro g v
  rw [c.intertwines]
  exact Prod.ext (LinearThree.matrixEquiv_natural _ _).symm
    (LinearThree.matrixEquiv_natural _ _).symm

theorem projectiveThree_marked_cubic
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ LinearThree.projectiveNatural) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v := by
  apply linearThree_marked_cubic d
  exact { actor := c.actor.trans LinearThree.projectiveEquiv
          coordinates := c.coordinates
          intertwines := fun g v => (c.intertwines g v).trans
            (LinearThree.projectiveEquiv_natural _ _).symm }

theorem doubleProjectiveThree_marked_cubic
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ
      (LinearThree.projectiveNatural.prod LinearThree.projectiveNatural)) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v := by
  apply doubleLinearThree_marked_cubic d
  refine { actor := c.actor.trans LinearThree.projectiveEquiv
           coordinates := c.coordinates
           intertwines := ?_ }
  intro g v
  rw [c.intertwines]
  exact Prod.ext (LinearThree.projectiveEquiv_natural _ _).symm
    (LinearThree.projectiveEquiv_natural _ _).symm

/-- The deleted-quotient convention for the natural S₃ module gives exactly
the same plane calculation, via the proved odd-degree core equivalence. -/
theorem symmetricThree_natural_marked_conclusions
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ (BinaryPermutation.naturalRepresentation (Fin 3))) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 2 ∧
      SymmetricThree.markerStabilizer ρ d.marker = (d.sylow : Subgroup D) ∧
      (SymmetricThree.markerStabilizer ρ d.marker).index = 3 := by
  let e := BinaryPermutation.coreEquivNatural (Fin 3) (by decide)
  apply SymmetricThree.marked_conclusions d
  refine { actor := c.actor
           coordinates := c.coordinates.trans e.symm
           intertwines := ?_ }
  intro g v
  apply e.injective
  simp only [LinearEquiv.trans_apply, e.apply_symm_apply]
  rw [BinaryPermutation.coreEquivNatural_equivariant, e.apply_symm_apply]
  exact c.intertwines g v

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
