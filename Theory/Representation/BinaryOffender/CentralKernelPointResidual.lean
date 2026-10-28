module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Point-stabilizer residuals through a fixed binary kernel

For an equivariant linear map with pointwise-fixed kernel, the two-residual
of the preimage of a quotient stabilizer fixes the original vector.
Functoriality of finite residuals gives equality of the embedded residual
images. The actor map can have a kernel; no module splitting is assumed.

Source application: Aschbacher–Smith, Theorem 12.6.2, printed pp.823–824,
where the linear map is the literal V → V/C_V(L) and the actor map is
L → L/C_L(V). This retains both projections in the residual comparison.
-/

public section

open Subgroup BinaryNaturalDual.VectorStabilizers
namespace Representation.BinaryOffender
variable {G H V W : Type*} [Group G] [Finite G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem map_stabilizer_residual_of_central_kernel
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
    (q : G →* H) (hq : Function.Surjective q)
    (f : V →ₗ[ZMod 2] W) (hf : ∀ g v, f (ρ g v) = σ (q g) (f v))
    (hk : f.ker ≤ ρ.invariants) (v : V) :
    ((pResidual 2 (representationStabilizer ρ v)).map
      (representationStabilizer ρ v).subtype).map q =
    (pResidual 2 (representationStabilizer σ (f v))).map
      (representationStabilizer σ (f v)).subtype := by
  let C := (representationStabilizer σ (f v)).comap q
  let E := (pResidual 2 C).map C.subtype
  have hE : E ≤ representationStabilizer ρ v := by
    have hv := fixed_of_pPerfect_central_kernel ρ E
      (isPPerfect_embedded_pResidual 2 C) f
      (fun w hw a => (hk hw) a.val) v (by
        intro a
        rw [hf]
        exact map_subtype_le (pResidual 2 C) a.property)
    intro a ha
    exact hv ⟨a,ha⟩
  have hEres : E ≤ (pResidual 2 (representationStabilizer ρ v)).map
      (representationStabilizer ρ v).subtype := by
    have hh := embedded_pResidual_mono 2 hE
    rw [(pResidual_eq_top_iff 2 E).mpr (isPPerfect_embedded_pResidual 2 C),
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hEmap : E.map q = (pResidual 2 (representationStabilizer σ (f v))).map
      (representationStabilizer σ (f v)).subtype := by
    dsimp only [E]
    rw [map_embedded_pResidual]
    have he : C.map q = representationStabilizer σ (f v) :=
      map_comap_eq_self_of_surjective hq _
    rw [he]
  apply le_antisymm
  · rw [map_embedded_pResidual]
    apply embedded_pResidual_mono
    rintro _ ⟨g,hg,rfl⟩
    change σ (q g) (f v) = f v
    rw [← hf, (show ρ g v = v from hg)]
  · rw [← hEmap]
    exact map_mono hEres
end Representation.BinaryOffender
