module
public import CFSG.Quasithin.ChapterE.Section04.InvariantSubmodule
public import CFSG.Quasithin.ChapterE.Section03.Parameters.ReducedAction

/-!
# Restricting the actual automizer to a faithful invariant subgroup

If W≤U are H-invariant and C_H(W)=C_H(U), conjugation on W identifies
the automizer on U with a subgroup of the automizer on W. The literal
inclusion of W into U transports fixed-space equalities. Thus an upper
bound on W gives the bound on all of U, including its fixed layers.
Source application: Aschbacher–Smith 12.4.1, printed p.812.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G]

theorem moduleA_induced_le_of_centralizer_eq
    (U W H : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 W]
    (hWU : W ≤ U) (hUH : U ≤ H)
    (hHU : H ≤ normalizer (U : Set G)) (hHW : H ≤ normalizer (W : Set G))
    (hc : centralizer (W.subgroupOf H : Set H) = centralizer (U.subgroupOf H : Set H)) :
    moduleA ((automizerRepresentation U).comp (inducedAutomizer U H).subtype) ≤
      moduleA ((automizerRepresentation W).comp (inducedAutomizer W H).subtype) := by
  let α := normalizedLocalAction U H hHU
  let β := normalizedLocalAction W H hHW
  have hα : Function.Surjective α := normalizedLocalAction_surjective U H hHU
  have hk : α.ker = β.ker := by
    rw [normalizedLocalAction_kernel U H hHU hUH,
      normalizedLocalAction_kernel W H hHW (hWU.trans hUH),hc]
  let f : inducedAutomizer U H →* inducedAutomizer W H :=
    α.liftOfSurjective hα ⟨β,hk.le⟩
  have he (h : H) : f (α h) = β h := by
    dsimp only [f]
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    obtain ⟨h,rfl⟩ := hα a
    have hh : h ∈ β.ker := by
      change β h = 1
      rw [←he]
      exact ha
    exact (show h ∈ α.ker from hk.symm ▸ hh)
  let ρ := (automizerRepresentation U).comp (inducedAutomizer U H).subtype
  let σ := (automizerRepresentation W).comp (inducedAutomizer W H).subtype
  let i : Additive W →ₗ[ZMod 2] Additive U :=
    (inclusion hWU).toAdditive.toZModLinearMap 2
  have hi : Function.Injective i := inclusion_injective hWU
  apply (moduleA_le_of_equivariant_embedding ρ (σ.comp f) i hi ?_).trans
    (moduleA_comp_le σ f hf)
  intro a w
  obtain ⟨h,rfl⟩ := hα a
  change i (σ (f (α h)) w) = ρ (α h) (i w)
  rw [he]
  rfl
end CFSG.Quasithin.ChapterE
