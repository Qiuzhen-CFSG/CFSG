module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.SL23Local.CoreClosure
public import Theory.SpecificGroups.SL2.CubicGeometry

/-!
# The intrinsic cubic geometry in the local SL₂(3) model

An actual equivalence L ≃ SL₂(3), together with X ≤ L and |X| = 3,
supplies all three fields of `CubicGeometry`: three other cubics,
generation by each pair, and transitivity under left conjugation by X.
The lower theorem proves these facts in the quaternion semidirect model
and transports them along the literal subgroup inclusion.

For the source core closure, `CoreModel.cubicGeometry` discharges the
geometry premise of `CoreModel.nonempty_pair`. The actual `CoreModel`
and the earlier three-local orders remain with that theorem's assembly
owner; no core identification or source order is assumed proved here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5, printed p.263.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
variable {G : Type*} [Group G]

/-- Cubic geometry from the actual SL₂(3) equivalence and original inclusions. -/
theorem cubicGeometry_of_equiv (L X : Subgroup G)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hXL : X ≤ L) (hX : Nat.card X = 3) : CubicGeometry L X := by
  obtain ⟨hc, hg, ht⟩ := SL23CubicGeometry.geometry_of_equiv L X e hXL hX
  exact ⟨hc, hg, ht⟩

variable [Finite G]

/-- The geometry premise of the source pair construction, with the core
identification retained explicitly. -/
theorem CoreModel.cubicGeometry {D : Seed G} (C : CoreModel D) :
    CubicGeometry (coreClosure D) D.X :=
  cubicGeometry_of_equiv _ _ C.equiv (X_le_coreClosure D) D.card_X

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
