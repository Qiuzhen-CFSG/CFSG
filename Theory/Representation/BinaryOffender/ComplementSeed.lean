module
public import Theory.Representation.BinaryOffender.ProjectedSeed
public import Theory.Representation.BinaryOffender.Homogeneous.Basic

/-!
# Central seeds in invariant complementary summands

An equivariant projection onto an invariant summand sends Sylow-fixed
vectors to Sylow-fixed vectors. If their ambient orbit spans the original
module, the projected orbit spans that summand. Thus the summand is
spanned by the intersection of its space with the original fixed space.
The Chapter15 consumer retains the literal central involution seed and
chosen proper four-space. Source: Aschbacher--Smith15.1.5(1), p.1087.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

theorem complement_seed_span (S : Subgroup D) (U R : Submodule (ZMod 2) V)
    (hU : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U)
    (hR : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ R) (hc : IsCompl U R)
    (hgen : Submodule.span (ZMod 2)
      {w | ∃ g v, v ∈ fixedSpace ρ S ∧ ρ g v = w} = ⊤) :
    Homogeneous.orbitSpan ρ ⊤ (fixedSpace ρ S ⊓ U) = U := by
  let p := U.projectionOnto R hc
  let e : V →ₗ[ZMod 2] V := U.subtype.comp p
  have he (g : D) (v : V) : e (ρ g v) = ρ g (e v) :=
    congrArg Subtype.val (complementProjection_intertwines ρ U R hU hR hc g v)
  have hfix {v : V} (hv : v ∈ fixedSpace ρ S) : e v ∈ fixedSpace ρ S ⊓ U := by
    refine ⟨?_,(p v).property⟩
    intro s
    change ρ s (e v) = e v
    rw [← he, show ρ s v = v from hv s]
  apply le_antisymm (Homogeneous.orbitSpan_le ρ inf_le_right hU)
  intro u hu
  have hg : u ∈ Submodule.span (ZMod 2)
      {w | ∃ g v, v ∈ fixedSpace ρ S ∧ ρ g v = w} := hgen ▸ Submodule.mem_top
  have hm : Submodule.span (ZMod 2)
      {w | ∃ g v, v ∈ fixedSpace ρ S ∧ ρ g v = w} ≤
      (Homogeneous.orbitSpan ρ ⊤ (fixedSpace ρ S ⊓ U)).comap e := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,v,hv,rfl⟩
    change e (ρ g v) ∈ Homogeneous.orbitSpan ρ ⊤ (fixedSpace ρ S ⊓ U)
    rw [he]
    exact le_iSup (fun a : (⊤ : Subgroup D) =>
      (fixedSpace ρ S ⊓ U).map (ρ a)) ⟨g,mem_top _⟩ ⟨e v,hfix hv,rfl⟩
  have hp : e u = u := congrArg Subtype.val
    (Submodule.projectionOnto_apply_of_mem_left hc hu)
  simpa only [Submodule.mem_comap,hp] using hm hg
end Representation.BinaryOffender

