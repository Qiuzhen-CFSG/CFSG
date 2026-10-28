module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Components
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.Setup
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The actual component action and its fixed subgroups

Restrict the supplied Sylow subgroup to the subnormal component and restrict
normalizer conjugation to the source central four-group. Its given trivial
centralizer kernel proves faithfulness. Each automorphism fixed subgroup is
identified with the component intersection in the literal element centralizer;
subnormal inheritance gives its self-centralizing two-core. Equivalences
transport the action, Sylow subgroup and fixed subgroups together.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the component
paragraph of 15.4.18, printed pp.1162–1163, using 1.1.3(1) and 1.1.5(3).
No component model or classification conclusion is assumed here.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch

/-- An intrinsic action with precisely the hypotheses consumed by the concrete
component calculations. The Sylow subgroup and action are actual witnesses. -/
structure FixedAction (L A : Type*) [Group L] [Group A] where
  sylow : Sylow 2 L
  action : A →* MulAut L
  faithful : Function.Injective action
  fixes : ∀ a : A, ∀ x : L, x ∈ (sylow : Subgroup L) → action a x = x
  characteristicTwo : LinearModels.CharacteristicTwoFixed action

/-- Transport the actual Sylow subgroup and all fixed subgroups together. -/
noncomputable def FixedAction.transport {L M A : Type*} [Group L] [Group M] [Group A] [Finite L]
    (d : FixedAction L A) (e : L ≃* M) : FixedAction M A where
  sylow := d.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  action := (MulAut.congr e).toMonoidHom.comp d.action
  faithful := (MulAut.congr e).injective.comp d.faithful
  fixes := by
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e (d.action a (e.symm (e y))) = e y
    rw [e.symm_apply_apply, d.fixes a y hy]
  characteristicTwo := LinearModels.characteristicTwoFixed_congr e d.action d.characteristicTwo

/-- The fixed subgroup of the actual conjugation action is the component's
intersection with the element centralizer, with relative subnormality. -/
theorem conjugation_fixed_characteristicTwo
    {I : Type*} [Group I] [Finite I] (L Z : Subgroup I)
    (hL : L.IsSubnormal) (ρ : Z →* MulAut L)
    (heval : ∀ z : Z, ∀ l : L, (ρ z l : I) = (z : I) * l * (z : I)⁻¹)
    (hc : ∀ z : Z, z ≠ 1 → HasCharacteristicTwo (centralizer ({(z : I)} : Set I))) :
    LinearModels.CharacteristicTwoFixed ρ := by
  intro z hz
  let C := centralizer ({(z : I)} : Set I)
  let D := L.subgroupOf C
  have hD : D.IsSubnormal := hL.subgroupOf
  have hself := subnormal_core_selfCentralizing (hc z hz) D hD
  let e : (ρ z).fixedSubgroup ≃* D := {
    toFun := fun x => ⟨⟨x.val, by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun l : L => (l : I))
        ((MulAut.mem_fixedSubgroup (ρ z) x.val).mp x.property)
      rw [heval] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x.val, x.property⟩, by
      apply (MulAut.mem_fixedSubgroup (ρ z) _).mpr
      apply Subtype.ext
      rw [heval]
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp x.val.property).symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hself

/-- The central Sylow four-group acts faithfully on a component and fixes its
actual Sylow intersection. Characteristic two descends through its subnormal
fixed subgroup, not through an arbitrary subgroup or quotient. -/
theorem exists_fixedAction_of_component
    {I : Type*} [Group I] [Finite I] (L Z : Subgroup I)
    (hL : Theory.GroupTheory.IsComponent I L) (S : Sylow 2 I)
    (hn : Z ≤ normalizer (L : Set I))
    (hfaithful : Z ⊓ centralizer (L : Set I) = ⊥)
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I))
    (hc : ∀ z : Z, z ≠ 1 → HasCharacteristicTwo (centralizer ({(z : I)} : Set I))) :
    ∃ d : FixedAction L Z,
      (d.sylow : Subgroup L) = (S : Subgroup I).subgroupOf L ∧
      ∀ z : Z, ∀ l : L, (d.action z l : I) = (z : I) * l * (z : I)⁻¹ := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.1
  obtain ⟨ρ, hρ, heval⟩ := exists_faithful_conjugation L Z hn hfaithful
  refine ⟨⟨P, ρ, hρ, ?_, conjugation_fixed_characteristicTwo L Z hL.1 ρ heval hc⟩,
    hP, heval⟩
  intro z l hl
  apply Subtype.ext
  rw [heval]
  apply mul_inv_eq_iff_eq_mul.mpr
  exact hSZ (show (l : I) ∈ (S : Subgroup I) from (show l ∈ (S : Subgroup I).subgroupOf L from hP ▸ hl)) z z.property

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
