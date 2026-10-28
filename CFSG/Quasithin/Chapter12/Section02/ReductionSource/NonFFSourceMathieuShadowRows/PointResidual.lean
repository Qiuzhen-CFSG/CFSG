module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.Automizer
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.PointResidual

/-!
# The PSL3(4) point quotient on the original M22 cocode orbit

The full automizer marking restricts on the original L to the marked simple
M22 component. The distinguished-vector centralizer therefore covers its
native PSL3(4) stabilizer; its kernel is the centralizer of the entire original
orbit, and its solvable residual moves that orbit. Neither L nor the orbit is
replaced by this local subgroup. These are the quotient and movement inputs
to C.2.8 in source 8.1.1; ambient point containment remains a separate step.

Source: Aschbacher--Smith H.15.1 and 8.1.1, printed pp.398,712,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Source 8.1.1's original cocode point residual, with its actual quotient
map, full centralizer kernel and whole-module movement. -/
theorem sourceOrbit_m22_cocode_point_residual
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i) :
    ∃ f : (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →* Matrix.PSL3Four.PSL,
      Function.Surjective f ∧
      (∀ c, ((m22WeightTwoVector_stabilizer_equiv i).symm (f c)).val =
        d.componentEquiv (D.orbitComponentHom ⟨c.val,c.property.1⟩)) ∧
      f.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf
        (L ⊓ centralizer ({(x : G)} : Set G)) ∧
      ⁅D.sourceOrbit,
        (solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = D.sourceOrbit := by
  let q : L →* M22 := d.componentEquiv.toMonoidHom.comp D.orbitComponentHom
  exact Chapter8.MathieuShadowRows.m22_point_residual D.sourceOrbit L
    D.sourceOrbit_component_normalizes q
    (d.componentEquiv.surjective.comp D.orbitComponentHom_surjective)
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
    (D.sourceOrbit_m22_component_coordinates m22CocodeRepresentation
      m22OuterCocodeRepresentation rfl d) x i hx

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
