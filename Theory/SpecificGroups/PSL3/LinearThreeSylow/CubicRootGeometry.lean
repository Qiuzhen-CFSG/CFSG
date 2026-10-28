module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicRootGeometry.Unitriangular
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicRootGeometry.Contract
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.GroupAction.OddCommutatorImage

/-!
# Sylow root and cubic calculations in PSL₃(F₄)

Sylow conjugacy identifies every actual Sylow two-subgroup with the literal
unitriangular model. Normal four-subgroups and cubic fixed points are then
computed in those coordinates. An outer automorphism cannot restrict to the
identity, by the checked pointwise Sylow-fixer theorem. Transporting all powers
of the actor carries the full commutator calculation back to the given Sylow.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree
open CubicRootGeometry
variable (F : Type*) [Field F] [Finite F]

/-- Sylow conjugacy supplies actual unitriangular coordinates for every Sylow. -/
theorem four_sylow_coordinates (hF : Nat.card F = 4) (P : Sylow 2 PSL(3,F)) :
    Nonempty (U F ≃* P) := by
  let P₀ := unipotentSylow F (by decide : 0 < 2) hF
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(3,F) P₀ P
  have hm : (unipotent F).map (MulAut.conj g).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  exact ⟨(unipotentEquiv F).trans (((MulAut.conj g).subgroupMap _).trans
    (MulEquiv.subgroupCongr hm))⟩

/-- An order-four subgroup normal in the specified Sylow is its ambient centre. -/
theorem normal_four_eq_sylow_center (hF : Nat.card F = 4)
    (P : Sylow 2 PSL(3,F)) (W : Subgroup PSL(3,F))
    (hWP : W ≤ P) (hn : (P : Subgroup PSL(3,F)) ≤ normalizer (W : Set PSL(3,F)))
    (hW : Nat.card W = 4) : W = (center P).map (P : Subgroup PSL(3,F)).subtype := by
  obtain ⟨e⟩ := four_sylow_coordinates F hF P
  let W' := W.subgroupOf (P : Subgroup PSL(3,F))
  let : W'.Normal := normal_subgroupOf_of_le_normalizer hn
  let K := W'.comap e.toMonoidHom
  have hK : Nat.card K = 4 := by
    change Nat.card (W'.comap e.toMonoidHom) = _
    rw [comap_equiv_eq_map_symm', card_map_of_injective e.symm.injective]
    rw [Nat.card_congr (subgroupOfEquivOfLe hWP).toEquiv, hW]
  have hKZ := normal_four_coordinates hF K hK
  have heq : W' = center P := by
    ext p
    have hc : e.symm p ∈ K ↔ e.symm p ∈ Z F := by rw [hKZ]
    have hm : e.symm p ∈ K ↔ p ∈ W' := by
      change e (e.symm p) ∈ W' ↔ _
      rw [e.apply_symm_apply]
    rw [hm, Z_eq_center] at hc
    refine hc.trans ⟨?_, ?_⟩
    · intro h
      simpa only [e.apply_symm_apply] using
        (show e (e.symm p) ∈ center P from
          (Subgroup.centerCongr e ⟨e.symm p, h⟩).property)
    · intro h
      exact (Subgroup.centerCongr e.symm ⟨p, h⟩).property
  rw [← heq]
  exact (map_subgroupOf_eq_of_le hWP).symm

/-- An outer cubic fixing the Sylow centre has no other fixed points and
has full commutator subgroup on that Sylow. -/
theorem outer_cubic_sylow_calculation (hF : Nat.card F = 4)
    (P : Sylow 2 PSL(3,F)) (α : MulAut PSL(3,F))
    (hout : α ∉ MulAut.innerSubgroup PSL(3,F)) (h3 : α ^ 3 = 1)
    (hP : (P : Subgroup PSL(3,F)).map α.toMonoidHom = P)
    (hZ : (center P).map (P : Subgroup PSL(3,F)).subtype ≤ α.fixedSubgroup) :
    (P : Subgroup PSL(3,F)) ⊓ α.fixedSubgroup =
        (center P).map (P : Subgroup PSL(3,F)).subtype ∧
      commutatorSubgroup (zpowers α) PSL(3,F) (P : Subgroup PSL(3,F)) = P := by
  obtain ⟨e⟩ := four_sylow_coordinates F hF P
  let αP : MulAut P := (α.subgroupMap (P : Subgroup PSL(3,F))).trans
    (MulEquiv.subgroupCongr hP)
  let β := MulAut.congr e.symm αP
  let f : U F →* PSL(3,F) := (P : Subgroup PSL(3,F)).subtype.comp e.toMonoidHom
  have hf (u : U F) : f (β u) = α (f u) := by
    change (e (e.symm (αP (e u))) : PSL(3,F)) = _
    rw [e.apply_symm_apply]
    rfl
  have hfi : Function.Injective f := (P : Subgroup PSL(3,F)).subtype_injective.comp e.injective
  have hfrange : f.range = (P : Subgroup PSL(3,F)) := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩; exact (e u).property
    · intro hp; exact ⟨e.symm ⟨p, hp⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  have hβ3 : β ^ 3 = 1 := by
    ext u : 1
    apply hfi
    have hh := congrArg (fun a : MulAut PSL(3,F) => a (f u)) h3
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply, hf] using hh
  have hβne : β ≠ 1 := by
    intro he
    have hfix : ∀ p ∈ P, α p = p := by
      intro p hp
      obtain ⟨u, hu⟩ := hfrange.ge hp
      rw [← hu, ← hf, he, MulAut.one_apply]
    obtain ⟨z, _, hz⟩ := exists_sylow_center_conj_of_equiv F (by decide : 0 < 2)
      hF (MulEquiv.refl _) P α hfix
    exact hout ⟨z, hz.symm⟩
  have hβZ : Z F ≤ β.fixedSubgroup := by
    intro u hu
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply hfi
    rw [hf]
    have heu : e u ∈ center P := (Subgroup.centerCongr e ⟨u, Z_eq_center F ▸ hu⟩).property
    exact (MulAut.mem_fixedSubgroup _ _).mp (hZ ⟨e u, heu, rfl⟩)
  have hfixed := cubic_fixed_coordinates hF β hβne hβ3 hβZ
  constructor
  · apply le_antisymm _ (le_inf (map_subtype_le _) hZ)
    rintro p ⟨hp, hfix⟩
    let u := e.symm ⟨p, hp⟩
    have hfu : f u = p := congrArg Subtype.val (e.apply_symm_apply _)
    have hu : u ∈ β.fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      apply hfi
      rw [hf, hfu, (MulAut.mem_fixedSubgroup _ _).mp hfix]
    have hc := (Subgroup.centerCongr e ⟨u, Z_eq_center F ▸ hfixed.le hu⟩).property
    exact ⟨e u, hc, hfu⟩
  · apply le_antisymm (Theory.GroupAction.OddCommutatorImage.cyclic_commutator_le _ α hP)
    have hn (n : ℕ) (u : U F) : f ((β ^ n) u) = (α ^ n) (f u) := by
      induction n generalizing u with
      | zero => rfl
      | succ n ih => rw [pow_succ', MulAut.mul_apply, hf, ih, pow_succ', MulAut.mul_apply]
    have hmap : (commutatorAction (zpowers β) (U F)).map f ≤
        commutatorSubgroup (zpowers α) PSL(3,F) (P : Subgroup PSL(3,F)) := by
      rw [commutatorAction, commutatorSubgroup, MonoidHom.map_closure, closure_le]
      rintro _ ⟨_, ⟨b, u, _, rfl⟩, rfl⟩
      obtain ⟨n, hn'⟩ := mem_powers_iff_mem_zpowers.mpr b.property
      apply Subgroup.subset_closure
      refine ⟨⟨α ^ n, pow_mem (mem_zpowers α) n⟩, f u, hfrange.le ⟨u, rfl⟩, ?_⟩
      change f (u⁻¹ * b.val u) = (f u)⁻¹ * (α ^ n) (f u)
      rw [← hn', map_mul, map_inv, hn]
    rw [cubic_commutator_coordinates hF β hβne hβ3 hβZ, ← MonoidHom.range_eq_map, hfrange] at hmap
    exact hmap

/-- The two intrinsic source calculations, with no additional model premises. -/
theorem fourSylowRootCalculations (hF : Nat.card F = 4) : FourSylowRootCalculations F where
  normal_four := normal_four_eq_sylow_center F hF
  cubic P a := outer_cubic_sylow_calculation F hF P
    (Matrix.PSL3.OuterSolvable.linearConj F a)
end Matrix.PSL3.LinearThree
