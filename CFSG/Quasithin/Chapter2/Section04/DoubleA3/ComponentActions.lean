module
public import Theory.SpecificGroups.AlternatingSix.AlternatingFourActions
public import Theory.SpecificGroups.PSL3Two.AlternatingFourFixer
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceSetup

/-!
# The marked action step for the paired cubic component

The same actual A₄ subgroup is used in both models of 2.4.32. The opposite
four-group cannot move a PSL₃(2) component while fixing that A₄ pointwise.
In the A₆ case its nontrivial involutory action supplies transposition
coordinates. The original normalizer of U₁ acts through natural S₆ under
those same coordinates.

The component absorption and two-model conclusion of 2.4.32, and the
noncentrality proved by the fusion argument of 2.4.34, remain explicit.
Source: Aschbacher–Smith, 2.4.35(1), printed p.548.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
variable {H : Type*} [Group H]

private theorem fixes_mapped_alternatingFour
    (K : Subgroup H) [K.Normal] (L : Subgroup H) (_hLK : L ≤ K)
    {A : Type*} [Group A] (e : K ≃* A) (u : H)
    (hu : u ∈ centralizer (L : Set H)) :
    ∀ l ∈ (L.subgroupOf K).map e.toMonoidHom,
      MulAut.congr e (MulAut.conjNormal (H := K) u) l = l := by
  rintro _ ⟨l,hl,rfl⟩
  change e (MulAut.conjNormal u (e.symm (e l))) = e l
  rw [e.symm_apply_apply]
  apply congrArg e
  apply Subtype.ext
  change u * (l : H) * u⁻¹ = l
  rw [←hu l hl, mul_inv_cancel_right]

/-- The PSL₃(2) alternative in 2.4.32 has no actor moving its component
while fixing the same actual alternating-four subgroup. -/
theorem centralizes_component_of_linearTwoSeven
    (K : Subgroup H) [K.Normal] (L : Subgroup H) (hLK : L ≤ K)
    (eL : L ≃* alternatingGroup (Fin 4)) (eK : K ≃* Matrix.PSL3Two.PSL)
    (u : H) (hu : u ∈ centralizer (L : Set H)) :
    u ∈ centralizer (K : Set H) := by
  let D := (L.subgroupOf K).map eK.toMonoidHom
  let eD : D ≃* alternatingGroup (Fin 4) :=
    ((L.subgroupOf K).equivMapOfInjective eK.toMonoidHom eK.injective).symm.trans
      ((subgroupOfEquivOfLe hLK).trans eL)
  have hf : MulAut.congr eK (MulAut.conjNormal (H := K) u) ∈
      fixingSubgroup (MulAut Matrix.PSL3Two.PSL) (D : Set Matrix.PSL3Two.PSL) :=
    (mem_fixingSubgroup_iff _).mpr (fixes_mapped_alternatingFour K L hLK eK u hu)
  rw [Matrix.PSL3Two.alternatingFour_fixer_eq_bot D eD, mem_bot] at hf
  have ha : MulAut.conjNormal (H := K) u = 1 :=
    (MulAut.congr eK).injective (hf.trans (map_one _).symm)
  intro k hk
  have he := congrArg (fun a : MulAut K => (a ⟨k,hk⟩ : H)) ha
  change u * k * u⁻¹ = k at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The literal noncentral actor from 2.4.34 selects A₆ from the two models
of 2.4.32 and supplies the actual transposition assertion in 2.4.35(1). -/
theorem transposition_of_two_component_models
    (K : Subgroup H) [K.Normal] (L V : Subgroup H) (hLK : L ≤ K)
    (eL : L ≃* alternatingGroup (Fin 4))
    (hmodel : Nonempty (K ≃* A6) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hV : ∀ v ∈ V, v ^ 2 = 1) (hVL : V ≤ centralizer (L : Set H))
    (hVK : ¬ V ≤ centralizer (K : Set H)) :
    ∃ (eK : K ≃* A6) (u : H), u ∈ V ∧
      ∃ σ : Equiv.Perm (Fin 6), σ.IsSwap ∧
        conjugationAction K eK u = permutationAction σ := by
  obtain ⟨u,hu,huc⟩ : ∃ u ∈ V, u ∉ centralizer (K : Set H) := by
    by_contra hn
    apply hVK
    intro u hu
    by_contra huc
    exact hn ⟨u,hu,huc⟩
  rcases hmodel with hm | hm
  · obtain ⟨eK⟩ := hm
    let D := (L.subgroupOf K).map eK.toMonoidHom
    let eD : D ≃* alternatingGroup (Fin 4) :=
      ((L.subgroupOf K).equivMapOfInjective eK.toMonoidHom eK.injective).symm.trans
        ((subgroupOfEquivOfLe hLK).trans eL)
    have hne : conjugationAction K eK u ≠ 1 := by
      intro he
      exact huc ((conjugationAction_ker K eK) ▸ he)
    have horder : orderOf (conjugationAction K eK u) = 2 := orderOf_eq_prime
      (by rw [←map_pow,hV u hu,map_one]) hne
    obtain ⟨a,σ,hσ,ha⟩ := AlternatingSix.alternatingFour_fixed_involution_coordinates
      D eD (conjugationAction K eK u) horder
      (fixes_mapped_alternatingFour K L hLK eK u (hVL hu))
    refine ⟨eK.trans a,u,hu,σ,hσ,?_⟩
    rw [←ha]
    apply MulEquiv.ext
    intro k
    rfl
  · obtain ⟨eK⟩ := hm
    exact (huc (centralizes_component_of_linearTwoSeven K L hLK eL eK u (hVL hu))).elim

/-- The selected coordinates also mark the whole original four-group
normalizer as natural; no independent choice of an A₆ copy is made. -/
theorem marked_actions_of_two_component_models
    (K : Subgroup H) [K.Normal] (L V U R : Subgroup H) [IsKleinFour U]
    (hLK : L ≤ K) (hUK : U ≤ K) (eL : L ≃* alternatingGroup (Fin 4))
    (hmodel : Nonempty (K ≃* A6) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hV : ∀ v ∈ V, v ^ 2 = 1) (hVL : V ≤ centralizer (L : Set H))
    (hVK : ¬ V ≤ centralizer (K : Set H))
    (hR : R ≤ normalizer (U : Set H)) :
    ∃ (eK : K ≃* A6) (u : H), u ∈ V ∧
      ∃ σ : Equiv.Perm (Fin 6), σ.IsSwap ∧
        conjugationAction K eK u = permutationAction σ ∧
        R.map (conjugationAction K eK) ≤ natural := by
  obtain ⟨eK,u,hu,σ,hσ,ha⟩ :=
    transposition_of_two_component_models K L V hLK eL hmodel hV hVL hVK
  exact ⟨eK,u,hu,σ,hσ,ha,
    conjugationAction_map_natural_of_normalizes_four K eK U R hUK hR⟩

end CFSG.Quasithin.Chapter2.DoubleA3
