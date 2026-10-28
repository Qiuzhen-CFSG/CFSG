module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Model
public import Theory.Representation.OrthogonalFourPlusMatrix.FirstCohomology
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# The original tensor quotient has vanishing first cohomology

The chosen marking identifies the actual quotient L₀/O₂(L₀) with the two
special-linear factors. The representation below uses that quotient map
and the original tensor coordinates from the source record. Transport of
first cohomology supplies the cohomology step in 9.2.2; the bound on the
quadratic ratio needed to identify Ω₁Z(Q) with V remains separate.

Source: Aschbacher--Smith 9.2.2, printed p.730.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

attribute [local irreducible] Binary.action

/-- The literal quotient of the original orbit actor, using its given kernel. -/
def coreQuotientEquiv :
    ((localOrbit T L) ⧸ pCore 2 (localOrbit T L)) ≃* Binary.G :=
  (QuotientGroup.quotientMulEquivOfEq m.kernel_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective m.quotient m.onto)

@[simp] theorem coreQuotientEquiv_mk (h : localOrbit T L) :
    m.coreQuotientEquiv (QuotientGroup.mk' (pCore 2 (localOrbit T L)) h) =
      m.quotient h := rfl

/-- The action of the original quotient on its marked tensor coordinates. -/
def coreQuotientAction : Representation (ZMod 2)
    ((localOrbit T L) ⧸ pCore 2 (localOrbit T L)) Binary.V :=
  Binary.action.comp m.coreQuotientEquiv.toMonoidHom

@[simp] theorem coreQuotientAction_mk (h : localOrbit T L) (v : Binary.V) :
    m.coreQuotientAction (QuotientGroup.mk' (pCore 2 (localOrbit T L)) h) v =
      sourceA5TensorAction m.quotient h v := by
  change Binary.action (m.coreQuotientEquiv _) v = Binary.action (m.quotient h) v
  rw [m.coreQuotientEquiv_mk]

/-- The quotient action is the conjugation action on the original full module. -/
theorem coreQuotientAction_coordinates (h : localOrbit T L) (v : D.fullModule) :
    (m.sectionData.coordinates ⟨h * v * (h : G)⁻¹,
      (mem_normalizer_iff.mp (m.sectionData.normalized h.property) v).mp v.property⟩).toAdd =
      m.coreQuotientAction (QuotientGroup.mk' (pCore 2 (localOrbit T L)) h)
        (m.sectionData.coordinates v).toAdd := by
  rw [m.coreQuotientAction_mk]
  exact m.sectionData.equivariant h v

/-- The original quotient, acting on the original tensor coordinates, has H¹=0. -/
theorem coreQuotient_subsingleton_H1 :
    Subsingleton (OneCohomology.H1 m.coreQuotientAction) := by
  let : Subsingleton (OneCohomology.H1 Binary.action) := Binary.tensor_subsingleton_H1
  let E := OneCohomology.H1Congr m.coreQuotientAction Binary.action
    m.coreQuotientEquiv (LinearEquiv.refl (ZMod 2) Binary.V) (fun _ _ => rfl)
  exact E.injective.subsingleton

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
