module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear tools for the trio calculation

A representation operator transports fixed spaces and displacement spans
along conjugation. A full general linear image is irreducible: an isomorphism
between the spans of two nonzero vectors extends to an ambient automorphism.
These elementary tools transfer the standard native trio calculation to every
trio in Aschbacher–Smith H.15.6, printed p.401.
-/

public section
open Representation
namespace Representation.BinaryOffender
noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

lemma fixedSpace_map_conj (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (g : G) :
    (fixedSpace ρ A).map (ρ g) = fixedSpace ρ (A.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩ ⟨_, a, ha, rfl⟩
    change ρ (g * a * g⁻¹) (ρ g v) = ρ g v
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, ρ.inv_self_apply]
    exact congrArg (ρ g) (show ρ a v = v from hv ⟨a, ha⟩)
  · intro v hv
    refine ⟨ρ g⁻¹ v, ?_, ρ.self_inv_apply g v⟩
    intro a
    have h := congrArg (ρ g⁻¹) (hv ⟨g * a.val * g⁻¹, a.val, a.property, rfl⟩)
    change ρ g⁻¹ (ρ (g * a.val * g⁻¹) v) = ρ g⁻¹ v at h
    change ρ a.val (ρ g⁻¹ v) = ρ g⁻¹ v
    simpa only [map_mul, Module.End.mul_apply, ρ.inv_self_apply] using h

lemma subspaceCommutator_top_map_conj (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (g : G) :
    (subspaceCommutator ρ ⊤ A).map (ρ g) =
      subspaceCommutator ρ ⊤ (A.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    change ρ g (ρ a v - v) ∈ subspaceCommutator ρ ⊤ (A.map (MulAut.conj g).toMonoidHom)
    have h : ρ (g * a * g⁻¹) (ρ g v) - ρ g v ∈
        subspaceCommutator ρ ⊤ (A.map (MulAut.conj g).toMonoidHom) :=
      Submodule.subset_span ⟨_, ⟨a, ha, rfl⟩, ρ g v, Submodule.mem_top, rfl⟩
    simpa only [map_sub, map_mul, Module.End.mul_apply, ρ.inv_self_apply] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, ha, rfl⟩, v, _, rfl⟩
    refine ⟨ρ a (ρ g⁻¹ v) - ρ g⁻¹ v,
      Submodule.subset_span ⟨a, ha, ρ g⁻¹ v, Submodule.mem_top, rfl⟩, ?_⟩
    change ρ g (ρ a (ρ g⁻¹ v) - ρ g⁻¹ v) = ρ (g * a * g⁻¹) v - v
    simp only [map_sub, map_mul, Module.End.mul_apply, ρ.self_inv_apply]

lemma irreducible_of_full_linear_image [Nontrivial V] (ρ : Representation (ZMod 2) G V)
    (hs : Function.Surjective ρ.asGroupHom) : IsIrreducible ρ := by
  refine ⟨fun P => ?_⟩
  by_cases hb : P = ⊥
  · exact Or.inl hb
  right
  have hn : P.toSubmodule ≠ ⊥ := fun h => hb (Subrepresentation.ext h)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff P.toSubmodule).mp hn
  apply top_unique
  intro y _
  by_cases hy : y = 0
  · rw [hy]; exact P.toSubmodule.zero_mem
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x hx0
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V y hy
  obtain ⟨f, hf⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  have hxy : f x = y := by
    have h := hf (ex 1)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
    simpa [ex, ey] using h.symm
  obtain ⟨g, hg⟩ := hs (LinearMap.GeneralLinearGroup.ofLinearEquiv f)
  have he : ρ g x = f x := LinearMap.congr_fun (congrArg Units.val hg) x
  rw [← hxy, ← he]
  exact P.apply_mem_toSubmodule g hx
end
end Representation.BinaryOffender
