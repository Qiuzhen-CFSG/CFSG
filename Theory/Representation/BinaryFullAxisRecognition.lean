module

public import Theory.Representation.BinaryTransvectionGroups.RootForms.Generation
public import Theory.Representation.BinaryTransvectionGroups.Duality
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducible binary actions containing a full axis group

A full common-axis group becomes a full transvection direction in the dual.
All such directions form an invariant subspace. Its annihilator in the
original irreducible module is zero, so the directions span the whole dual.
Gaussian elimination then gives every linear automorphism. This proves the
precise full-axis specialization used in G.10.4 without the unrestricted
full-action statement of G.3.1.
-/

public section
open Module BinaryLinear BinaryTransvectionGroups
open BinaryLinear.FourCentralizerOvergroups
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Irreducibility and one full common-axis group force the original action
onto GL(V), in every binary dimension. -/
theorem full_linear_action_of_irreducible_axis (ρ : Representation (ZMod 2) G V)
    [IsIrreducible ρ] (f : Module.Dual (ZMod 2) V) (hf : f ≠ 0)
    (haxis : ∀ a : f.ker, ∃ g : G, ∀ v, ρ g v = v + f v • (a : V)) :
    ∀ e : V ≃ₗ[ZMod 2] V, ∃ g : G, ∀ v, ρ g v = e v := by
  let aρ : G →* BinaryLinear.GL V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  let μ := contragredient.comp aρ
  let D := directions μ.range
  have hfD : f ∈ D := by
    intro φ hφ
    let a := (Module.evalEquiv (ZMod 2) V).symm φ
    have ha : f a = 0 := by
      rw [Module.apply_evalEquiv_symm_apply]
      exact hφ
    obtain ⟨g, hg⟩ := haxis ⟨a, ha⟩
    have he : aρ g = transvection a f ha := by
      ext v
      exact hg v
    refine ⟨g, ?_⟩
    change contragredient (aρ g) = transvection f φ hφ
    rw [he]
    ext l v
    change l (v + f v • a) = l v + φ l * f v
    rw [map_add, map_smul, Module.apply_evalEquiv_symm_apply]
    simp only [smul_eq_mul, mul_comm]
  let C : Subrepresentation ρ := {
    toSubmodule := D.dualCoannihilator
    apply_mem_toSubmodule g v hv := by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro l hl
      have hm : ρ.dual g⁻¹ l ∈ D :=
        direction_apply hl (show μ g⁻¹ ∈ μ.range from ⟨g⁻¹, rfl⟩)
      have he := hv (ρ.dual g⁻¹ l) hm
      change l (ρ (g⁻¹)⁻¹ v) = 0 at he
      simpa only [inv_inv] using he }
  have hC : C = ⊥ := by
    rcases eq_bot_or_eq_top C with he | he
    · exact he
    · exfalso
      apply hf
      ext v
      have hv : v ∈ C.toSubmodule := by
        rw [he]
        trivial
      exact (Submodule.mem_dualCoannihilator v).mp hv f hfD
  have hD : D = ⊤ := by
    have he : D.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule hC
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := D), he,
      Submodule.dualAnnihilator_bot]
  have hμ : μ.range = ⊤ := BinaryTransvectionGroups.eq_top_of_directions_eq_top μ.range hD
  intro e
  obtain ⟨g, hg⟩ := MonoidHom.range_eq_top.mp hμ (contragredient e)
  have he : aρ g = e := contragredient_injective hg
  exact ⟨g, fun v => congrArg (fun a : BinaryLinear.GL V => a v) he⟩

end Representation
