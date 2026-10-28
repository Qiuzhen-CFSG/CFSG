module

public import Theory.Representation.BinaryOffender.MarkedOrbitCore
public import Theory.Representation.BinaryOffender.DualDisplacement
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Two-cores on submodules of a symplectic orbit span

A nondegenerate invariant pairing maps V onto the dual of every invariant
subspace U. If a Sylow-fixed point generates V, its image generates U*.
The faithful action image on U acts faithfully also on U*, so its normal
two-core fixes the generating orbit and is trivial. The pairing map is the
literal restriction of the original form; there is no chosen dual action.

Source application: Aschbacher--Smith, G.10.3, printed p.357.
-/

@[expose] public section
open Subgroup Module
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  (B : LinearMap.BilinForm (ZMod 2) V)

/-- Pairing against the actual invariant subspace. -/
def submodulePairing (U : Subrepresentation ρ) : V →ₗ[ZMod 2] Module.Dual (ZMod 2) U.toSubmodule :=
  U.toSubmodule.subtype.dualMap.comp B

omit [Finite G] in
theorem submodulePairing_surjective (hB : B.Nondegenerate) (U : Subrepresentation ρ) :
    Function.Surjective (submodulePairing ρ B U) :=
  (LinearMap.dualMap_surjective_of_injective U.toSubmodule.subtype_injective).comp
    (B.toDual hB).surjective

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Invariance of the original form gives the genuine inverse-dual action. -/
theorem submodulePairing_equivariant
    (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (U : Subrepresentation ρ) (g : G) (v : V) :
    submodulePairing ρ B U (ρ g v) = U.toRepresentation.dual g (submodulePairing ρ B U v) := by
  ext u
  change B (ρ g v) u = B v (ρ g⁻¹ u)
  have he := hinv g v (ρ g⁻¹ (u : V))
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using he

/-- B.2.13 and duality applied to the literal action image on each submodule. -/
theorem submodule_actionImage_twoCore_eq_bot_of_sylow_fixed_orbit
    (hB : B.Nondegenerate) (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (S : Sylow 2 G) (v : V) (hfix : ∀ s : S, ρ s v = v)
    (hspan : Submodule.span (ZMod 2) {w | ∃ g : G, ρ g v = w} = ⊤)
    (U : Subrepresentation ρ) : pCore 2 (actionImage U.toRepresentation) = ⊥ := by
  let π := actionHom U.toRepresentation
  let τ := imageRepresentation U.toRepresentation
  let S' := S.mapSurjective (f := π) U.toRepresentation.asGroupHom.rangeRestrict_surjective
  let q := submodulePairing ρ B U
  have hqe (g : G) (w : V) : q (ρ g w) = τ.dual (π g) (q w) :=
    submodulePairing_equivariant ρ B hinv U g w
  apply twoCore_eq_bot_of_sylow_fixed_span τ.dual
    (faithful_dual τ (imageRepresentation_injective U.toRepresentation)) S'
    (Submodule.span (ZMod 2) {q v})
  · apply Submodule.span_le.mpr
    rintro _ rfl s
    obtain ⟨g, hg, he⟩ := s.property
    change τ.dual s (q v) = q v
    rw [← he]
    exact (hqe g v).symm.trans (congrArg q (hfix ⟨g, hg⟩))
  · have hqspan : Submodule.span (ZMod 2) {w | ∃ g : G, q (ρ g v) = w} = ⊤ := by
      have he := congrArg (Submodule.map q) hspan
      rw [Submodule.map_span, Submodule.map_top,
        LinearMap.range_eq_top.mpr (submodulePairing_surjective ρ B hB U)] at he
      convert he using 2
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨ρ g v, ⟨g, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, rfl⟩
    apply top_unique
    rw [← hqspan]
    apply Submodule.span_mono
    rintro _ ⟨g, rfl⟩
    exact ⟨π g, q v, Submodule.mem_span_singleton_self _, (hqe g v).symm⟩

end Representation.BinaryOffender
