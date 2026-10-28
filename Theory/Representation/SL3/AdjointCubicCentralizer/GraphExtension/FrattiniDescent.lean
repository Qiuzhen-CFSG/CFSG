module
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension
public import Theory.Representation.SL3.AdjointCubicCentralizer.FixedLevi
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.Frattini.PGroup

/-!
# The graph-extension consequence for the full core quotient

The input retains the component quotient, the projective projection square,
and a binary marking of the whole core Frattini quotient. Its representation
is constructed by descent of the literal ambient conjugation action. The
kernel-corrected crossing equation supplies an intertwiner for the same
component automorphism, even when the crossing does not normalize the cubic
extension subgroup. Graph compatibility proves the representation ordinary
under the original coordinates. The existing diagonal group marker then
gives the fixed-space bound at the original cubic.

This conditional source adapter is also available for a component and extension
without the legacy secondary-source record or its strict-enlargement field.

Source: Aschbacher–Smith B.4.14, printed p.98, and the terminal argument
for original 4.3.2, pp.618–619. This is a conditional representation consequence,
not a construction of the earlier-source witnesses from MSData.
-/

open Matrix Representation Subgroup
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
namespace Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {N F : Type*} [Group N] [Field F] [CharP F 2]
attribute [local instance] ZMod.algebra

private def markedAut {M : Type*} [Group M] (e : M ≃* Multiplicative (TraceZero F)) :
    MulAut M →* Module.End (ZMod 2) (TraceZero F) where
  toFun a := AddMonoidHom.toZModLinearMap 2
    ({ toFun v := (e (a (e.symm (Multiplicative.ofAdd v)))).toAdd
       map_zero' := by
         change (e (a (e.symm 1))).toAdd = 0
         rw [map_one,map_one,map_one]
         rfl
       map_add' v w := by
         change (e (a (e.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w)))).toAdd = _
         rw [map_mul,map_mul,map_mul]
         rfl } : TraceZero F →+ TraceZero F)
  map_one' := by
    apply LinearMap.ext
    intro v
    change (e (e.symm (Multiplicative.ofAdd v))).toAdd = v
    rw [e.apply_symm_apply]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change (e (a (b (e.symm (Multiplicative.ofAdd v))))).toAdd =
      (e (a (e.symm (e (b (e.symm (Multiplicative.ofAdd v))))))).toAdd
    rw [e.symm_apply_apply]

variable (B E : Subgroup N) [B.Normal] (hBE : B ≤ E)

abbrev Core := B.pCoreIn 2
abbrev Frattini := Core B ⧸ frattini (Core B)

instance core_normal : (Core B).Normal := inferInstanceAs ((pCore 2 B).map B.subtype).Normal

def coreAction : N →* MulAut (Frattini B) :=
  normalQuotientAction (Core B) (frattini (Core B))

/-- The action is literally ambient conjugation on the core Frattini quotient.
This equation lets source producers use their original quotient-action witnesses. -/
theorem coreAction_eq : coreAction B =
    normalQuotientAction (Core B) (frattini (Core B)) := by
  unfold coreAction
  rfl

/-- Earlier-source witnesses on the whole original core quotient. The crossing
is allowed to leave E; its corrected action, rather than subgroup normalization,
descends through the projective map. -/
structure FrattiniGraphData where
  componentMarking : (B ⧸ pCore 2 B) ≃* PSL(3,F)
  projection : E →* ProjGenLinGroup (Fin 3) F
  onto : Function.Surjective projection
  componentSquare : ∀ b : B, projection (inclusion hBE b) =
    ProjectiveSpecialLinearGroup.toPGL (componentMarking (QuotientGroup.mk' (pCore 2 B) b))
  coordinates : Frattini B ≃* Multiplicative (TraceZero F)
  componentEquivariant : ∀ (b : B) v,
    (coordinates (coreAction B (b : N) v)).toAdd =
      projectiveSpecialAdjoint F (componentMarking (QuotientGroup.mk' (pCore 2 B) b))
        (coordinates v).toAdd
  kernelDescent : projection.ker ≤ ((coreAction B).comp E.subtype).ker
  crossing : N
  actor : MulAut PSL(3,F)
  actor_eq : actor = (MulAut.congr componentMarking)
    (normalQuotientAction B (pCore 2 B) crossing)
  correction : GL (Fin 3) F
  field : F ≃+* F
  graph_eq : actor = linearConj F correction * graph F * fieldAction F field
  crossingDescent : ∀ g : E, ∃ g' : E,
    projection g' = conjugatePGL F actor
      (graphActor_normalizes F actor correction field graph_eq) (projection g) ∧
    coreAction B (crossing * (g : N) * crossing⁻¹) = coreAction B (g' : N)

variable {B E hBE} [Finite F]

def FrattiniGraphData.quotientAction (d : FrattiniGraphData (F := F) B E hBE) :
    ProjGenLinGroup (Fin 3) F →* MulAut (Frattini B) :=
  d.projection.liftOfSurjective d.onto ⟨(coreAction B).comp E.subtype,d.kernelDescent⟩

omit [CharP F 2] [Finite F] in
theorem FrattiniGraphData.quotientAction_projection
    (d : FrattiniGraphData (F := F) B E hBE) (g : E) :
    d.quotientAction (d.projection g) = coreAction B (g : N) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

def FrattiniGraphData.representation (d : FrattiniGraphData (F := F) B E hBE) :
    Representation (ZMod 2) (ProjGenLinGroup (Fin 3) F) (TraceZero F) :=
  (markedAut d.coordinates).comp d.quotientAction

omit [Finite F] in
theorem FrattiniGraphData.representation_component
    (d : FrattiniGraphData (F := F) B E hBE) :
    d.representation.comp ProjectiveSpecialLinearGroup.toPGL =
      restrictScalars (k := ZMod 2) (projectiveSpecialAdjoint F) := by
  apply MonoidHom.ext
  intro g
  obtain ⟨z,rfl⟩ := d.componentMarking.surjective g
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
  apply LinearMap.ext
  intro v
  change markedAut d.coordinates (d.quotientAction
    (ProjectiveSpecialLinearGroup.toPGL (d.componentMarking (QuotientGroup.mk' _ b)))) v = _
  rw [←d.componentSquare,d.quotientAction_projection]
  exact (d.componentEquivariant b (d.coordinates.symm (Multiplicative.ofAdd v))).trans
    (by rw [d.coordinates.apply_symm_apply]; rfl)

theorem FrattiniGraphData.ordinary (d : FrattiniGraphData (F := F) B E hBE)
    (hF : Nat.card F = 4) :
    d.representation = restrictScalars (k := ZMod 2) (projectiveAdjoint F) := by
  let A : Representation (ZMod 2) N (TraceZero F) := (markedAut d.coordinates).comp (coreAction B)
  let u := LinearEquiv.ofBijective (A d.crossing) (A.apply_bijective d.crossing)
  apply ordinary_of_graphActor F hF d.representation d.representation_component
    d.actor (graphActor_normalizes F d.actor d.correction d.field d.graph_eq)
    d.correction d.field d.graph_eq u
  intro p v
  obtain ⟨g,rfl⟩ := d.onto p
  obtain ⟨g',hg',hg⟩ := d.crossingDescent g
  change A d.crossing (markedAut d.coordinates (d.quotientAction (d.projection g)) v) =
    markedAut d.coordinates (d.quotientAction _) (A d.crossing v)
  rw [←hg',d.quotientAction_projection,d.quotientAction_projection]
  have he : A (d.crossing * (g : N) * d.crossing⁻¹) = A (g' : N) :=
    congrArg (markedAut d.coordinates) hg
  change A d.crossing (A (g : N) v) = A (g' : N) (A d.crossing v)
  rw [←he,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,A.inv_self_apply]

theorem FrattiniGraphData.ordinary_action (d : FrattiniGraphData (F := F) B E hBE)
    (hF : Nat.card F = 4) (g : E) (v : Frattini B) :
    (d.coordinates (coreAction B (g : N) v)).toAdd =
      projectiveAdjoint F (d.projection g) (d.coordinates v).toAdd := by
  have he := LinearMap.congr_fun
    (DFunLike.congr_fun (d.ordinary hF) (d.projection g)) (d.coordinates v).toAdd
  change markedAut d.coordinates (d.quotientAction (d.projection g)) _ = _ at he
  rw [d.quotientAction_projection] at he
  change (d.coordinates (coreAction B (g : N) (d.coordinates.symm (d.coordinates v)))).toAdd = _ at he
  rwa [d.coordinates.symm_apply_apply] at he

variable [Finite N]

/-- The lower bound is on the same whole Frattini quotient and the same cubic;
the group marker is independent of the module-extension recognition. -/
theorem FrattiniGraphData.fixed_card_ge (d : FrattiniGraphData (F := F) B E hBE)
    (hF : Nat.card F = 4) {X : Type*} [Group X] (j : X →* E)
    (x : X) (hx : zpowers x = ⊤) (ω : Fˣ)
    (hdiag : d.projection (j x) = ProjGenLinGroup.mk (diagonalUnit F ω)) :
    let : MulDistribMulAction X (Frattini B) :=
      MulDistribMulAction.compHom _ ((coreAction B).comp (E.subtype.comp j))
    256 ≤ Nat.card (FixedPoints.subgroup X (Frattini B)) := by
  let : MulDistribMulAction X (Frattini B) :=
    MulDistribMulAction.compHom _ ((coreAction B).comp (E.subtype.comp j))
  let e : Frattini B ≃ TraceZero F :=
    { toFun v := (d.coordinates v).toAdd
      invFun w := d.coordinates.symm (Multiplicative.ofAdd w)
      left_inv v := d.coordinates.symm_apply_apply v
      right_inv w := congrArg Multiplicative.toAdd (d.coordinates.apply_symm_apply (Multiplicative.ofAdd w)) }
  apply fixed_card_ge_of_adjoint_generator F hF x hx ω e
  intro v
  change (d.coordinates (coreAction B (j x : N) v)).toAdd =
    projectiveAdjoint F (ProjGenLinGroup.mk (diagonalUnit F ω)) (d.coordinates v).toAdd
  rw [←hdiag]
  exact d.ordinary_action hF (j x) v

end
end Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
