module
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.SymplecticOrbitCore
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Lagrangian duality on literal binary sections

A nondegenerate invariant alternating form on R/N pairs a Lagrangian
section S/N perfectly with R/S. Restricting the original coordinates and
then pairing against them constructs both sections. The coordinate equation
records the original pairing, and the action on R/S is the inverse dual.

Source application: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964, for U₀/U_H and V_H/U₀.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {H R N : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- A preserved alternating pairing identifies the complementary literal
section with the inverse dual of a Lagrangian section. -/
theorem exists_lagrangian_dual_sections
    (p : BinaryConjugationSection H R N ρ) (S : Subgroup G)
    (hNS : N ≤ S) (hSR : S ≤ R) (hS : H ≤ normalizer S)
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hinv : ∀ h x y, B (ρ h x) (ρ h y) = B x y)
    (hlag : B.orthogonal (p.imageSpace S) = p.imageSpace S) :
    ∃ (σ : Representation (ZMod 2) H (p.imageSpace S))
      (s : BinaryConjugationSection H S N σ)
      (t : BinaryConjugationSection H R S σ.dual),
      (∀ u : S, ((s.coordinates u).toAdd : W) =
        (p.coordinates (inclusion hSR u)).toAdd) ∧
      ∀ v : R, ∀ u : S,
        (t.coordinates v).toAdd (s.coordinates u).toAdd =
          B (p.coordinates v).toAdd (p.coordinates (inclusion hSR u)).toAdd := by
  let P : Subrepresentation ρ := {
    toSubmodule := p.imageSpace S
    apply_mem_toSubmodule h := p.imageSpace_apply_mem S h (hS h.property) }
  let σ := P.toRepresentation
  let s : BinaryConjugationSection H S N σ := {
    section_le := hSR.trans p.section_le
    kernel_le := hNS
    normalized := hS
    coordinates := {
      toFun u := Multiplicative.ofAdd ⟨(p.coordinates (inclusion hSR u)).toAdd,
        (p.mem_imageSpace_iff S _).mpr ⟨inclusion hSR u,u.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one p.coordinates)
      map_mul' u v := by
        apply Subtype.ext
        change (p.coordinates (inclusion hSR (u*v))).toAdd =
          (p.coordinates (inclusion hSR u)).toAdd + (p.coordinates (inclusion hSR v)).toAdd
        simp only [map_mul, toAdd_mul] }
    onto := by
      intro u
      obtain ⟨v,hv,he⟩ := (p.mem_imageSpace_iff S u.toAdd.val).mp u.toAdd.property
      exact ⟨⟨v,hv⟩,Subtype.ext he⟩
    kernel_eq := by
      ext u
      change (⟨(p.coordinates (inclusion hSR u)).toAdd,_⟩ : p.imageSpace S) = 0 ↔ (u:G) ∈ N
      rw [Subtype.ext_iff]
      exact p.coordinates_eq_one_iff _
    equivariant h u := by apply Subtype.ext; exact p.equivariant h (inclusion hSR u) }
  let F := BinaryOffender.submodulePairing ρ B P
  have hk (v : W) : F v = 0 ↔ v ∈ p.imageSpace S := by
    rw [←hlag]
    constructor
    · intro hv u hu
      have hh := congrArg (fun f : Module.Dual (ZMod 2) P.toSubmodule => f ⟨u,hu⟩) hv
      exact hB.eq_iff.mp hh
    · intro hv
      ext u
      exact hB.eq_iff.mpr (hv u u.property)
  let t : BinaryConjugationSection H R S σ.dual := {
    section_le := p.section_le
    kernel_le := hSR
    normalized := p.normalized
    coordinates := F.toAddMonoidHom.toMultiplicative.comp p.coordinates
    onto := (BinaryOffender.submodulePairing_surjective ρ B hnd P).comp p.onto
    kernel_eq := by
      ext v
      change F (p.coordinates v).toAdd = 0 ↔ (v:G) ∈ S
      rw [hk]
      exact p.coordinates_mem_imageSpace_iff_of_kernel_le S hNS v
    equivariant h v := by
      change F (p.coordinates _).toAdd = σ.dual h (F (p.coordinates v).toAdd)
      rw [p.equivariant]
      exact BinaryOffender.submodulePairing_equivariant ρ B hinv P h _ }
  exact ⟨σ,s,t,fun _ => rfl,fun _ _ => rfl⟩
end Representation.BinaryConjugationSection
