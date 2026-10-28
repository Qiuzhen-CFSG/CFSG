module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.RootRigidity
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.SylowAlignment
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment

/-!
# Inner-field coverage for the actual G₂ model

Over a finite field of characteristic two with more than two elements, every
abstract automorphism of the split-octonion G₂ model is inner times the genuine
coefficientwise field action. Sylow conjugacy and the concrete root-frame
alignment give an inner correction preserving all eight labelled root groups.
The coordinate rigidity theorem then identifies that correction as torus times
field. Undoing the conjugation gives an actual semilinear preimage, with its
model element and multiplication order explicit. This includes the field of
order four and assumes no prescribed action on root parameters.

The conditional reductions are retained below; the final theorems discharge
their alignment premise using the imported geometric result.

Source: the G₂ automorphism input used in Aschbacher--Smith F.1.12, printed
pp.263--264. The coefficient action, actual roots and torus are the licensed
ATLAS model and its checked extensions imported above.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open RootDiagonal LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

/-- An explicit inner correction into the root frame supplies an actual
inner-field expression for the original automorphism. -/
theorem exists_inner_field_of_root_alignment (a : MulAut (Model F)) (g : Model F)
    (hg : PreservesRootGroups (MulAut.conj g * a)) :
    ∃ (x : Model F) (σ : F ≃+* F), a = MulAut.conj x * fieldAction σ := by
  obtain ⟨u, v, σ, h⟩ := eq_torus_field_of_preservesRootGroups (MulAut.conj g * a) hg
  refine ⟨g⁻¹ * torus (u ^ 2 * v) (u * v), σ, ?_⟩
  calc
    a = MulAut.conj g⁻¹ * (MulAut.conj g * a) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = MulAut.conj g⁻¹ * (MulAut.conj (torus (u ^ 2 * v) (u * v)) * fieldAction σ) :=
      congrArg (fun c => MulAut.conj g⁻¹ * c) h
    _ = _ := by rw [← mul_assoc, ← map_mul]

/-- Coverage follows once the geometric root alignment is supplied for every
abstract automorphism. The parameter rigidity has already been discharged. -/
theorem semilinearAction_surjective_of_root_alignment
    (halign : ∀ a : MulAut (Model F), ∃ g : Model F,
      PreservesRootGroups (MulAut.conj g * a)) :
    Function.Surjective (semilinearAction (F := F)) := by
  intro a
  obtain ⟨g, hg⟩ := halign a
  obtain ⟨x, σ, h⟩ := exists_inner_field_of_root_alignment a g hg
  exact ⟨⟨x, σ⟩, h.symm⟩

/-- The outstanding alignment need only treat automorphisms fixing the standard
Sylow subgroup. No restriction on the correcting model element is required. -/
theorem semilinearAction_surjective_of_sylow_root_alignment [Finite F]
    (halign : ∀ a : MulAut (Model F),
      unipotent.map a.toMonoidHom = unipotent →
        ∃ g : Model F, PreservesRootGroups (MulAut.conj g * a)) :
    Function.Surjective (semilinearAction (F := F)) := by
  apply semilinearAction_surjective_of_root_alignment
  intro a
  obtain ⟨g, hg, _⟩ := exists_sylow_parabolic_alignment a
  obtain ⟨u, hu⟩ := halign (MulAut.conj g * a) hg
  refine ⟨u * g, ?_⟩
  simpa only [map_mul, mul_assoc] using hu

end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage

namespace Atlas.G2.LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every abstract automorphism of the actual G₂ model over a finite field of
characteristic two and order greater than two is in the inner-field image. -/
theorem semilinearAction_surjective (hq : 2 < Nat.card F) :
    Function.Surjective (semilinearAction (F := F)) :=
  InnerFieldCoverage.semilinearAction_surjective_of_sylow_root_alignment
    (InnerFieldCoverage.root_frame_alignment_of_sylow hq)

/-- The inner-field decomposition uses an element of the actual octonion
automorphism model and coefficientwise field transport. -/
theorem exists_inner_field (hq : 2 < Nat.card F) (a : MulAut (Model F)) :
    ∃ (g : Model F) (σ : F ≃+* F), a = MulAut.conj g * fieldAction σ := by
  obtain ⟨z, hz⟩ := semilinearAction_surjective hq a
  exact ⟨z.left, z.right, hz.symm⟩

end Atlas.G2.LieAutomorphismExtensions
