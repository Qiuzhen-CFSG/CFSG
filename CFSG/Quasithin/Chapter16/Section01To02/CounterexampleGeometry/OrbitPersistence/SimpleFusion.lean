module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.ModelContracts
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.Suzuki.InvolutionFusion

/-!
# Involution fusion for the rank-one component alternatives

The finite-field PSL₂ calculation covers both linear alternatives, and the
concrete Suzuki ovoid supplies the Suzuki alternative. Transporting these
results through the isomorphisms stored in `RankOneComponentModel` proves
that every pair of involutions in the component is conjugate.

This is the intrinsic model fact used in case (I) of Aschbacher–Smith,
Lemma 16.2.6, printed p.1174 (combined manuscript of 1 March 2004).
The ambient orbit and persistence argument is assembled by the parent module.
-/

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
universe v
variable {L : Type v} [Group L]

private theorem linear_involutions_isConj {q : ℕ} (model : ClassicalGroup.IsPSL L 2 q)
    (a b : L) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := model
  have hc := Theory.PSL2.involutions_isConj (e a) (e b)
    (by simpa using ha) (by simpa using hb)
  simpa using e.symm.toMonoidHom.map_isConj hc

/-- Each of the three actual rank-one model families has a single involution class. -/
public theorem RankOneComponentModel.involutions_isConj (model : RankOneComponentModel L)
    (a b : L) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  cases model with
  | linear_even n hn iso => exact linear_involutions_isConj iso a b ha hb
  | linear_odd p hp hlarge iso => exact linear_involutions_isConj iso a b ha hb
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    have hc := BenderSuzuki.MatrixGroups.suzuki_involutions_isConj m (by omega)
      (e a) (e b) (by simpa using ha) (by simpa using hb)
    simpa using e.symm.toMonoidHom.map_isConj hc

end CFSG.Quasithin.Chapter16.CounterexampleGeometry
