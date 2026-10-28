module

public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Geometry.Eigenspaces
public import Theory.SpecificGroups.PSp4Three.ReducibleSubgroups.LinearAction
public import Theory.SpecificGroups.PSp4Three.ReducibleSubgroups.SmallFactors

/-!
# Noncentral involution centralizers in Sp₄(3)

A noncentral involution on the actual symplectic four-space has two
nondegenerate alternating sign spaces. Their even dimensions and the
exclusion of scalar involutions make both spaces two-dimensional. Every
centralizing matrix preserves them, and its two restrictions determine it
on the whole space. Thus its centralizer embeds in the product of their
general linear groups, both isomorphic to the solvable group GL₂(3).

The eigenspace and solvability results are reused from `Geometry.Eigenspaces`
and `ReducibleSubgroups.SmallFactors`; no conjugacy classification is needed.
This supplies the involution-centralizer premise of
`lift_core_extraspecial_of_small_centralizers`. The centralizer is in Sp₄(3),
before taking its quotient by the center.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed
pp.4 and 482 of `refs/quasithin.pdf`.
-/

noncomputable section
namespace Matrix.PSp4Three.NontrivialTwoCore
open Geometry.LinearInvolution ReducibleLinear

/-- Every noncentral element of square one in the concrete Sp₄(3) has
a solvable centralizer. -/
public theorem noncentral_involution_centralizer_isSolvable
    (t : Sp 2 (ZMod 3)) (ht : t ^ 2 = 1)
    (hn : t ∉ Subgroup.center (Sp 2 (ZMod 3))) :
    Group.IsSolvable (Subgroup.centralizer ({t} : Set (Sp 2 (ZMod 3)))) := by
  let T := (toLinear t).toLinearMap
  have hi : Function.Involutive T := by
    intro x
    change t • (t • x) = x
    rw [← mul_smul, ← pow_two, ht, one_smul]
  have hp : T ≠ LinearMap.id := by
    intro h
    apply hn
    apply scalar_is_central t 1
    intro x
    simpa [T] using LinearMap.congr_fun h x
  have hm : T ≠ -LinearMap.id := by
    intro h
    apply hn
    apply scalar_is_central t (-1)
    intro x
    simpa [T] using LinearMap.congr_fun h x
  have hd := finranks_eq_two form form_alternating form_nondegenerate T hi
    (preserves t) (by decide) (by simp [Vector, Index]) hp hm
  let C := Subgroup.centralizer ({t} : Set (Sp 2 (ZMod 3)))
  let ρ : C →* (Vector 2 (ZMod 3) ≃ₗ[ZMod 3] Vector 2 (ZMod 3)) :=
    toLinear.comp C.subtype
  have hc (g : C) (x : Vector 2 (ZMod 3)) : T (ρ g x) = ρ g (T x) := by
    have he := Subgroup.mem_centralizer_singleton_iff.mp g.prop
    change t • (g.val • x) = g.val • (t • x)
    rw [← mul_smul, ← mul_smul, he]
  have hP (g : C) : ∀ x ∈ plus T, ρ g x ∈ plus T := by
    intro x hx
    rw [mem_plus] at hx ⊢
    rw [hc, hx]
  have hM (g : C) : ∀ x ∈ minus T, ρ g x ∈ minus T := by
    intro x hx
    rw [mem_minus] at hx ⊢
    rw [hc, hx, map_neg]
  let r := (restriction ρ (plus T) hP).prod (restriction ρ (minus T) hM)
  have hr : Function.Injective r := by
    intro g h he
    apply Subtype.ext
    apply ext_action
    intro x
    obtain ⟨⟨p, m⟩, rfl⟩ := (decomposition T hi (by decide)).surjective x
    have hp' : ρ g p.val = ρ h p.val :=
      congrArg (fun a : (plus T ≃ₗ[ZMod 3] plus T) ×
        (minus T ≃ₗ[ZMod 3] minus T) => (a.1 p).val) he
    have hm' : ρ g m.val = ρ h m.val :=
      congrArg (fun a : (plus T ≃ₗ[ZMod 3] plus T) ×
        (minus T ≃ₗ[ZMod 3] minus T) => (a.2 m).val) he
    change ρ g (p.val + m.val) = ρ h (p.val + m.val)
    rw [map_add, map_add, hp', hm']
  let := linearEquiv_isSolvable_finrank_two hd.1
  let := linearEquiv_isSolvable_finrank_two hd.2
  exact Group.isSolvable_of_isSolvable_injective hr

end Matrix.PSp4Three.NontrivialTwoCore
