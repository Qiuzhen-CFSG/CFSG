module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.AmbientGeometry
public import Theory.Representation.HexacodeAction.PlaneStabilizer

/-!
# Application to the actual definite-plane normalizer

The constructed coordinates identify the Thompson image with the even
hexacode group and recognize each particular source definite plane. The
proved hexacode stabilizer calculation then gives its A₅ quotient, which
the normalizer lifting theorem transports through the original quotient
map. Thus the conclusion concerns the literal normalizer in J(G₀), without
assuming injectivity of the quotient on that subgroup.

This is an application of the independent stabilizer calculation, not a
new model classification. The ambient normalizer bound and solvability
contradiction completing 15.3.1 remain with the source assembly owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.1155 (PDF p.1172), the final two sentences of the proof of 15.3.1.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

universe u
variable {G : Type u} [Group G] [Finite G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}

omit [Finite G] in
/-- The existing model stabilizer quotient and lifting theorem applied to
the actual source plane and actual Thompson image in the constructed coordinates. -/
theorem HexacodeCoordinates.exists_surjective_localPlaneNormalizer
    (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)
    (i : OrthogonalPlaneIndex)
    (hplane : Representation.Hexacode.IsFullWeightScalarPlane
      ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map c.vectors.toLinearMap)) :
    ∃ f : (thompsonGroup G₀ ⊓ normalizer (localPlane G₀ M V d i : Set G₀) :
        Subgroup G₀) →* alternatingGroup (Fin 5), Function.Surjective f := by
  obtain ⟨f, hf⟩ := Representation.Hexacode.exists_surjective_planeStabilizer_A5 _ hplane
  let e := planeStabilizerEquiv_hexacode (V.subgroupOf G₀) hC hcore
    (thompsonGroup G₀) (localPlane G₀ M V d i)
    c.actor c.vectors c.equivariant c.thompson_image
  exact exists_surjective_planeNormalizer_to_A5 (V.subgroupOf G₀) hC hcore
    (thompsonGroup G₀) (localPlane G₀ M V d i)
    ((localPlane_le G₀ M V d i).trans le_normalClosure)
    (f.comp e.toMonoidHom) (hf.comp e.surjective)

omit [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- The non-S₃ classifiers and aligned earlier geometry yield an A₅ quotient
of the actual source plane normalizer. Every coordinate and stabilizer premise
of the lifting theorem is discharged. -/
theorem EarlierGeometry.exists_surjective_localPlaneNormalizer
    {a : Intersection.SourceInput (V.subgroupOf G₀)} (g : EarlierGeometry d a)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3)))
    (i : OrthogonalPlaneIndex) :
    ∃ f : (thompsonGroup G₀ ⊓ normalizer (localPlane G₀ M V d i : Set G₀) :
      Subgroup G₀) →* alternatingGroup (Fin 5), Function.Surjective f := by
  let _ := g.moduleClosure_elementary
  obtain ⟨c, hc⟩ := g.recognize
    hG₀ classificationF classificationB hnot
  exact c.exists_surjective_localPlaneNormalizer i (hc i)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction
