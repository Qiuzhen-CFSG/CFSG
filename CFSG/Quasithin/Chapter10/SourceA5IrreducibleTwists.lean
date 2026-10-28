module
public import Theory.Representation.AlternatingFiveTwists
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Automorphism invariance for every binary simple A₅ module

The complete field-four classifier reduces each nontrivial irreducible
module to the natural or deleted model. Their specified linear twists
transport back to the original vector space. For a group with A₅ two-core
quotient, normal two-subgroups act trivially on irreducible binary modules,
so the same conclusion descends and lifts through the literal quotient.

Source: Aschbacher–Smith, G.9.3 and the A₅ case of D.3.6,
combined manuscript, printed pp.354 and196.
-/

@[expose] public section
open Representation Subgroup
noncomputable section
namespace CFSG.Quasithin.Chapter10
local instance sourceA5IrreducibleTwistsAlgebra : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
variable {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem twist_of_marking {K W : Type*} [Group K]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) J V) (τ : Representation (ZMod 2) K W)
    (f : J ≃* K) (u : σ.Equiv (τ.comp f.toMonoidHom)) (a : MulAut J)
    (c : W ≃+ W)
    (hc : ∀ g v, c (τ g v) = τ ((f.symm.trans (a.trans f)) g) (c v)) :
    ∃ b : V ≃ₗ[ZMod 2] V, ∀ g v, b (σ g v) = σ (a g) (b v) := by
  let b := u.toLinearEquiv.toAddEquiv.trans (c.trans u.toLinearEquiv.toAddEquiv.symm)
  let B : V ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective (b.toAddMonoidHom.toZModLinearMap 2) b.bijective
  have hB (v : V) : u (B v) = c (u v) := u.toLinearEquiv.apply_symm_apply _
  refine ⟨B, ?_⟩
  intro g v
  apply u.injective
  change u (B (σ g v)) = u (σ (a g) (B v))
  have hu (g : J) (v : V) : u (σ g v) = τ (f g) (u v) :=
    Representation.IntertwiningMap.isIntertwining σ _ u.toIntertwiningMap g v
  rw [hB, hu, hu, hB]
  change c (τ (f g) (u v)) = τ (f (a g)) (c (u v))
  simpa only [MulEquiv.trans_apply, f.symm_apply_apply] using hc (f g) (u v)

theorem source_a5_irreducible_twist
    (σ : Representation (ZMod 2) J V) [σ.IsIrreducible]
    (e : J ≃* alternatingGroup (Fin 5)) (a : MulAut J) :
    ∃ c : V ≃ₗ[ZMod 2] V, ∀ g v, c (σ g v) = σ (a g) (c v) := by
  classical
  by_cases hσ : ∃ g, σ g ≠ 1
  · obtain ⟨_, h | h⟩ := ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives σ e hσ
    · obtain ⟨f, ⟨u⟩⟩ := h
      obtain ⟨c, hc⟩ := AlternatingFiveTwists.natural_twist (f.symm.trans (a.trans f))
      exact twist_of_marking σ _ f u a c.toAddEquiv hc
    · obtain ⟨f, ⟨u⟩⟩ := h
      obtain ⟨c, hc⟩ := AlternatingFiveTwists.deleted_twist (f.symm.trans (a.trans f))
      exact twist_of_marking σ _ f u a c.toAddEquiv hc
  · have hh (g : J) : σ g = 1 := not_ne_iff.mp (fun hn => hσ ⟨g, hn⟩)
    exact ⟨LinearEquiv.refl _ _, fun g v => by simp only [hh, LinearEquiv.refl_apply]⟩

theorem source_a5_irreducible_core_quotient_twist
    [Finite J] (σ : Representation (ZMod 2) J V) [σ.IsIrreducible]
    (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) (a : MulAut J) :
    ∃ c : V ≃ₗ[ZMod 2] V, ∀ g v, c (σ g v) = σ (a g) (c v) := by
  have hk := normal_p_subgroup_le_ker σ (pCore 2 J) pCore_isPGroup
  let τ := quotientOfLEKer σ (pCore 2 J) hk
  let : τ.IsIrreducible := (quotientOfLEKer_irreducible_iff σ _ hk).mpr inferInstance
  obtain ⟨c, hc⟩ := source_a5_irreducible_twist τ e (quotientAut (pCore 2 J) a)
  refine ⟨c, ?_⟩
  intro g v
  have hh := hc (QuotientGroup.mk' (pCore 2 J) g) v
  rw [quotientAut_apply_mk] at hh
  exact hh

end CFSG.Quasithin.Chapter10
