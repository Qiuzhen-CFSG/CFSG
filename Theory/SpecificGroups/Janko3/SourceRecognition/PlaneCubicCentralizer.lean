module
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneTransport
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point
import all Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCubicWitness

/-!
# The full original linear complement centralizes the marked cubic

This is an intentional internal API extension of PlaneCubicWitness: its
already checked scalar-coordinate calculation is reused privately through
`import all`, while the public conclusion exposes only the original groups
and literal field embedding. No coordinate proof or marked element is copied.
The full complement containment lets its actual derived subgroup enter the
canonical derived A₆ factor of the cubic centralizer.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
namespace Sporadic.Janko3.SourceRecognition.PlaneTransport

/-- The whole chosen natural complement centralizes the original scalar cubic. -/
theorem field_cubic_centralizes_complement
    {G : Type*} [Group G]
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : Model →* G) (hj : FieldEmbedding A C a j) (c : C) :
    Commute (j cubic) ((c : normalizer (A : Set G)) : G) := by
  obtain ⟨s,hs,hsz⟩ := cubic_coordinates A C l a ha j hj
  have hh : Commute s c := by
    apply l.injective
    rw [map_mul,map_mul,hsz]
    exact Matrix.GeneralLinearGroup.scalar_commute b (l c)
  let k : C →* G := (normalizer (A : Set G)).subtype.comp C.subtype
  have hm := hh.map k
  simpa only [k,MonoidHom.comp_apply,coe_subtype,hs] using hm

end Sporadic.Janko3.SourceRecognition.PlaneTransport
