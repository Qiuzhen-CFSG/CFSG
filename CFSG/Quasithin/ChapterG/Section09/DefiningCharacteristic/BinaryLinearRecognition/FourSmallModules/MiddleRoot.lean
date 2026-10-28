module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.MiddleRoot.Cyclic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight

/-!
# Recognition of the middle-root binary SL₄ module

The explicit local highest-vector relations construct an equivalence with the
exterior square of the natural four-space. The checked exceptional PSL₄(2)–A₈
comparison intertwines its exterior action with the deleted permutation action
on the same split quadratic six-space. Composing those actual equivalences
recognizes the literal orthogonal A₈ representation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(12),
printed pp.354,356--357. The ATLAS comparison retains its attribution and license
in its owning modules. The full small-module classification is assembled by
the parent development; this module proves its middle-root branch.
-/

public section

open Representation Atlas.Order20160A8
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Middle-root singleton support recognizes the literal orthogonal A₈ module. -/
theorem LocalHighestVector.quasiequivalent_orthogonalEight_of_middle
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    [FiniteDimensional (ZMod 2) V] {v : V}
    (h : LocalHighestVector ρ {1} v) (hv : v ≠ 0) :
    Quasiequivalent ρ Representation.BinaryLinearRecognition.orthogonalEightAction := by
  let E := h.middleRootExteriorEquiv hv
  let e : Group ≃* alternatingGroup (Fin 8) :=
    sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  let f : V ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 3 (ZMod 2) :=
    E.toLinearEquiv.symm.trans Exterior.coordinates
  refine ⟨e, f, ?_⟩
  intro g x
  have hi := LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' g) x
  change E.toLinearEquiv.symm (ρ g x) = MiddleRoot.exterior g (E.toLinearEquiv.symm x) at hi
  change Exterior.coordinates (E.toLinearEquiv.symm (ρ g x)) =
    (DeletedEight.orthogonalHom (e g).val).val (Exterior.coordinates (E.toLinearEquiv.symm x))
  rw [hi]
  have he := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal g
  change DeletedEight.orthogonalHom (e g).val = Exterior.toOrthogonal g at he
  rw [he]
  change Exterior.coordinates (Bivectors.exteriorMap g.val (E.toLinearEquiv.symm x)) =
    Exterior.coordinates (Bivectors.exteriorMap g.val
      (Exterior.coordinates.symm (Exterior.coordinates (E.toLinearEquiv.symm x))))
  rw [LinearEquiv.symm_apply_apply]

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
