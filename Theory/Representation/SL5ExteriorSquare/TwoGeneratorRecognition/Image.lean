module
public import Theory.Representation.SL5ExteriorSquare.TwoGeneratorRecognition.Generators
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer.Graph

/-!
# Generation and orbits in the genuine exterior square

Transport the two checked natural generators through the actual exterior-power
representation. Their image generates the full exterior image, hence has exactly
the two nonzero orbits already proved in the local geometry (Aschbacher–Smith,
12.5.5, printed p.819). Faithfulness is reused from `ExteriorNormalizer.Graph`.
-/

@[expose] public noncomputable section
namespace Representation.SL5ExteriorSquare.TwoGeneratorRecognition
open SL5TenDimensional

/-- The actual exterior action as a homomorphism into linear equivalences. -/
def exteriorHom : Group →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    (exteriorAction 2).asGroupHom

@[simp] theorem exteriorHom_toLinearMap (g : Group) :
    (exteriorHom g).toLinearMap = exteriorAction 2 g := rfl

@[simp] theorem exteriorHom_apply (g : Group) (v : V) :
    exteriorHom g v = exteriorAction 2 g v := rfl

theorem exteriorHom_injective : Function.Injective exteriorHom :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).injective.comp
    (ExteriorNormalizer.exteriorAction_injective 0)

theorem range_le_of_generators {K : Type*} [_root_.Group K]
    (f : Group →* K) (H : Subgroup K) (h0 : f A0 ∈ H) (h1 : f A1 ∈ H) :
    f.range ≤ H := by
  have h : H.comap f = ⊤ := eq_top_of_contains _ h0 h1
  rintro _ ⟨g,rfl⟩
  exact (show g ∈ H.comap f from h ▸ Subgroup.mem_top g)

/-- Generation in the actual exterior square, not merely in a tagged module. -/
theorem closure_exterior_generators :
    Subgroup.closure ({exteriorHom A0,exteriorHom A1} : Set (V ≃ₗ[ZMod 2] V)) =
      exteriorHom.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx
    · exact ⟨A0,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨A1,rfl⟩
  · exact range_le_of_generators _ _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

/-- Every exterior transporter is a word in the two given exterior matrices. -/
theorem generated_orbit_iff (v w : V) :
    (∃ a ∈ Subgroup.closure ({exteriorHom A0,exteriorHom A1} : Set (V ≃ₗ[ZMod 2] V)),
      a v = w) ↔ InExteriorOrbit v w := by
  rw [closure_exterior_generators]
  constructor
  · rintro ⟨a,⟨g,rfl⟩,h⟩
    exact ⟨g,h⟩
  · rintro ⟨g,h⟩
    exact ⟨exteriorHom g,⟨g,rfl⟩,h⟩

/-- The generated action has exactly the two existing nonzero exterior orbits. -/
theorem generated_nonzero_orbits (v : V) (hv : v ≠ 0) :
    ((∃ a ∈ Subgroup.closure ({exteriorHom A0,exteriorHom A1} : Set (V ≃ₗ[ZMod 2] V)),
       a decomposable = v) ∧ ¬ InExteriorOrbit nondecomposable v) ∨
    ((∃ a ∈ Subgroup.closure ({exteriorHom A0,exteriorHom A1} : Set (V ≃ₗ[ZMod 2] V)),
       a nondecomposable = v) ∧ ¬ InExteriorOrbit decomposable v) := by
  simpa only [generated_orbit_iff] using exterior_orbits_exactly_one v hv

end Representation.SL5ExteriorSquare.TwoGeneratorRecognition
