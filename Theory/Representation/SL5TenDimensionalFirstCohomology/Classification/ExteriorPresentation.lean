module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.Seeds
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.GrassmannMultilinear
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.GrassmannOrbit
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Universal exterior presentation: final assembly

The binary Grassmann-symbol construction produces an alternating map on frames
from a vector satisfying the stabilizer and line relations in `Seeds`. The
universal property of exterior powers then turns that map into a linear map.
Equivariance on frames extends to equivariance on the entire exterior power
because decomposable vectors span it.

Thus the local seed relations suffice to construct an intertwiner into any
binary representation, with no dimension or irreducibility assumption.

The presentation is used in the module identification of Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

/-- An equivariant alternating frame assignment gives the intertwiner required
by the exterior presentation. -/
theorem intertwiner_of_equivariant_alternating_map
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (a : Fin 2) (v : V)
    (A : (Fin 5 → ZMod 2) [⋀^Fin (degree a)]→ₗ[ZMod 2] V)
    (hframe : A (frame a) = v)
    (hequiv : ∀ (g : Group) (w : Fin (degree a) → Fin 5 → ZMod 2),
      A (fun i => Matrix.mulVec g.val (w i)) = ρ g (A w)) :
    ∃ f : (exteriorAction (degree a)).IntertwiningMap ρ, f (seed a) = v := by
  let F : ExteriorModule (degree a) →ₗ[ZMod 2] V :=
    exteriorPower.alternatingMapLinearEquiv A
  have hF (g : Group) (x : ExteriorModule (degree a)) :
      F (exteriorAction (degree a) g x) = ρ g (F x) := by
    have hLin : F.comp (exteriorAction (degree a) g) = (ρ g).comp F := by
      apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _
        (exteriorPower.ιMulti_span (ZMod 2) (degree a) (Fin 5 → ZMod 2))).mpr
      rintro ⟨_, ⟨w, rfl⟩⟩
      simp only [LinearMap.comp_apply, F, exteriorAction_ιMulti,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      exact hequiv g w
    exact LinearMap.congr_fun hLin x
  refine ⟨F.intertwiningMap_of_isIntertwiningMap (exteriorAction (degree a)) ρ hF, ?_⟩
  simpa only [LinearMap.toIntertwiningMap, seed, F,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] using hframe

/-- The stabilizer and Grassmann-line relations present the binary exterior
square and cube: any vector satisfying them is the image of the standard seed
under an equivariant linear map. The target may be any binary representation. -/
theorem intertwiner_of_seed
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (a : Fin 2) (v : V)
    (hv : HasExteriorSeed ρ a v) :
    ∃ f : (exteriorAction (degree a)).IntertwiningMap ρ, f (seed a) = v := by
  obtain ⟨C⟩ := grassmannAssignment_of_seed ρ a v hv
  obtain ⟨A, hA⟩ := C.exists_alternatingMap
  apply intertwiner_of_equivariant_alternating_map ρ a v A
  · exact (hA (frame a)).trans C.frame_value
  · intro g w
    rw [hA, hA]
    exact C.equivariant g w

end Representation.SL5TenDimensional.Classification
