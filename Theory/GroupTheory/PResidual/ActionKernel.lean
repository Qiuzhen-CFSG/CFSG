module
public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.PPerfectHom

/-!
# Residual movement and p-group action kernels

A normal subgroup containing a p-subgroup outside the intrinsic p-core
supplements a Sylow whenever that Sylow's proper overgroups lie in its
normalizer. The normal subgroup therefore contains the p-residual.
Consequently a residually nontrivial action cannot kill an escaping
p-subgroup. Burnside's Frattini automorphism kernel also shows that this
residual movement survives passage to the Frattini quotient.

Source application: DGS, *Groups and Graphs* (1985), 8.4, printed p.138.
The literal section consumer is `DGS85.CommutingNontrivial.RadiusThreeResidual`.
-/

public section
namespace Subgroup
variable {D : Type*} [Group D] {p : ℕ}

/-- A normal subgroup containing an escaping p-subgroup contains the p-residual.
The marked Sylow has no proper overgroup outside its normalizer. -/
theorem pResidual_le_normal_of_sylow_overgroup_escape
    (S : Sylow p D)
    (hu : ∀ X : Subgroup D, (S : Subgroup D) ≤ X → X ≠ ⊤ →
      X ≤ normalizer (S : Set D))
    (N A : Subgroup D) [N.Normal] (hA : IsPGroup p A)
    (hAN : A ≤ N) (hAQ : ¬ A ≤ pCore p D) : pResidual p D ≤ N := by
  have hs : N ⊔ (S : Subgroup D) = ⊤ := by
    by_contra hn
    have hnS : N ≤ normalizer (S : Set D) :=
      le_sup_left.trans (hu _ le_sup_right hn)
    have hAS : A ≤ S := by
      have hh := hA.inf_normalizer_sylow S
      rw [inf_eq_left.mpr (hAN.trans hnS)] at hh
      exact inf_eq_left.mp hh.symm
    have hcore : (normalizer (S : Set D)).pCoreIn p = (S : Subgroup D) := by
      apply le_antisymm
      · have hh := pCoreIn_le_sylow (normalizer (S : Set D))
          (S.subtype (S : Subgroup D).le_normalizer)
        intro x hx
        obtain ⟨y,hy,rfl⟩ := hh hx
        exact hy
      · exact le_pCoreIn_of_normalizes S.isPGroup' (S : Subgroup D).le_normalizer le_rfl
    have he := Theory.GroupTheory.AmalgamLocalCores.core_eq_edge_inf_kernel S
      (normalizer (S : Set D)) (S : Subgroup D).le_normalizer
    rw [hcore] at he
    exact hAQ (he.symm ▸ le_inf hAS (hAN.trans (normal_le_normalCore.mpr hnS)))
  exact sInf_le ⟨inferInstance,
    isPGroup_quotient_of_sup_eq_top N (S : Subgroup D) S.isPGroup' hs⟩

/-- An action moved by the residual has no additional p-elements in its kernel
outside the intrinsic p-core, under the marked Sylow overgroup condition. -/
theorem pGroup_inf_kernel_le_pCore_of_residual_not_le
    (S : Sylow p D)
    (hu : ∀ X : Subgroup D, (S : Subgroup D) ≤ X → X ≠ ⊤ →
      X ≤ normalizer (S : Set D))
    {C : Type*} [Group C] (f : D →* C) (hr : ¬ pResidual p D ≤ f.ker)
    (A : Subgroup D) (hA : IsPGroup p A) : A ⊓ f.ker ≤ pCore p D := by
  by_contra hn
  exact hr (pResidual_le_normal_of_sylow_overgroup_escape S hu f.ker
    (A ⊓ f.ker) (hA.to_le inf_le_left) inf_le_right hn)

end Subgroup

namespace MonoidHom
variable {D X : Type*} [Group D] [Finite D] [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime]

/-- Residual movement survives on the original finite p-group's Frattini quotient. -/
theorem residual_not_le_frattini_action_kernel
    (hp : IsPGroup p X) (α : D →* MulAut X)
    (hr : ¬ pResidual p D ≤ α.ker) :
    ¬ pResidual p D ≤ ((Subgroup.quotientAut (frattini X)).comp α).ker := by
  intro hh
  let R := pResidual p D
  let f : R →* (Subgroup.quotientAut (frattini X)).ker :=
    (α.comp R.subtype).codRestrict _ (fun r => hh r.property)
  have hf := (Subgroup.isPPerfect_pResidual p).hom_eq_one_of_isPGroup
    (Subgroup.isPGroup_quotientAut_frattini_kernel hp) f
  apply hr
  intro r hr
  exact congrArg (fun g : R →* (Subgroup.quotientAut (frattini X)).ker =>
    ((g ⟨r,hr⟩ : (Subgroup.quotientAut (frattini X)).ker) : MulAut X)) hf

end MonoidHom

