module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.TrioCardinality
public import Theory.Mathieu.M24.LocalGeometry.Stabilizers
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Markings

/-!
# Transport of the native far-line orbit

The literal M₂₄ action preserves trio-sextet incidence and coplanarity.
The established sextet conjugator therefore reduces the native far-line
transitivity statement to the standard sextet, retaining the same point
permutation on every object. This is the transport used by AS91 (3.8) and
its application in (7.8); no far-line orbit assertion is assumed by Input.

Source: Aschbacher–Segev (1991), (3.8), (7.8), pp.595,605.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.Stabilizers
open scoped Pointwise

@[simp] theorem smulLine_parts (g : M24) (l : Line) : (g • l).parts = g • l.parts := rfl

theorem incident_transport (g : M24) {l m : Line} {π σ : Plane}
    (hl : m.parts = g • l.parts) (hπ : σ.parts = g • π.parts)
    (hi : Incident l π) : Incident m σ := by
  intro A hA
  rw [hl] at hA
  obtain ⟨B,hB,rfl⟩ := Finset.mem_smul_finset.mp hA
  obtain ⟨C,hC,D,hD,hCD,rfl⟩ := hi B hB
  refine ⟨g • C, hπ.symm ▸ Finset.smul_mem_smul_finset hC,
    g • D, hπ.symm ▸ Finset.smul_mem_smul_finset hD,
    (MulAction.injective g).ne hCD, Finset.smul_finset_union ..⟩

theorem coplanar_transport (g : M24) {l m a b : Line}
    (ha : a.parts = g • l.parts) (hb : b.parts = g • m.parts)
    (hc : Coplanar l m) : Coplanar a b := by
  obtain ⟨π,hl,hm⟩ := hc
  exact ⟨conjugateSextet g π, incident_transport g ha rfl hl,
    incident_transport g hb rfl hm⟩

/-- A line is near a plane precisely when it is coplanar with one of its
incident trios. -/
def NearPlane (π : Plane) (l : Line) : Prop := ∃ k, Incident k π ∧ Coplanar k l

theorem nearPlane_transport (g : M24) {l m : Line} {π σ : Plane}
    (hl : m.parts = g • l.parts) (hπ : σ.parts = g • π.parts)
    (hn : NearPlane π l) : NearPlane σ m := by
  obtain ⟨k,hk,hc⟩ := hn
  exact ⟨g • k, incident_transport g rfl hπ hk, coplanar_transport g rfl hl hc⟩

def FarTransitive : Prop := ∀ (π : Plane) (l m : Line),
  ¬ NearPlane π l → ¬ NearPlane π m →
    ∃ g : M24, g • π.parts = π.parts ∧ g • l.parts = m.parts

/-- Transitivity for the standard sextet suffices, using the same actual
native point permutation on both the sextet and the trios. -/
theorem farTransitive_of_standard
    (hstd : ∀ l m : Line, ¬ NearPlane standardSextet l → ¬ NearPlane standardSextet m →
      ∃ g : M24, g • standardSextet.parts = standardSextet.parts ∧ g • l.parts = m.parts) :
    FarTransitive := by
  intro π l m hl hm
  obtain ⟨a,ha⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator π
  have hn (t : Line) (ht : ¬ NearPlane π t) : ¬ NearPlane standardSextet (a⁻¹ • t) := by
    intro hn
    apply ht
    exact nearPlane_transport a (by simp) ha.symm hn
  obtain ⟨g,hg,hgm⟩ := hstd (a⁻¹ • l) (a⁻¹ • m) (hn l hl) (hn m hm)
  refine ⟨a * g * a⁻¹, ?_, ?_⟩
  · rw [← ha]
    simp only [mul_smul, inv_smul_smul, hg]
  · have hgm' : g • (a⁻¹ • l.parts) = a⁻¹ • m.parts := hgm
    simpa only [mul_smul, smul_inv_smul] using congrArg (a • ·) hgm'
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
