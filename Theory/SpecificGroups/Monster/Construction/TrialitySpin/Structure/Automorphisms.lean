/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CodeAction
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.LoopLifts

/-!
# The concrete standard-automorphism group

The existing standard permutations form a subgroup and project to the faithful
Golay coordinate group. The sign of the image of the all-ones loop element is a
group character, whose kernel consists exactly of the even automorphisms.
Source: Aschbacher, Section 14, pp. 58–59; Section 27, pp. 143–144.

Adapted from Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerStandardAutomorphisms.lean`, `Atlas/Fischer/ParkerStandardParity.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Changes: CFSG module imports, local triality namespace, Lean 4.33 proof syntax,
and compatibility with the existing concrete `IsStandard` predicate.
-/

@[expose] public section

namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes

/-- The existing predicate expressed using the restricted code equivalence. -/
theorem isStandard_iff (e : Equiv.Perm ParkerLoop) : IsStandard e ↔
    (∀ x y, e (parkerLoopMultiply x y) = parkerLoopMultiply (e x) (e y)) ∧
    (∀ s : Bit, e (0, s) = (0, s)) ∧
    ∃ g : Mathieu24CodeModel, ∀ x, (e x).1 = parkerCodeEquiv g x.1 := by
  constructor
  · rintro ⟨hm, hs, g, hg⟩
    exact ⟨hm, hs, g, fun x => Subtype.ext (hg x)⟩
  · rintro ⟨hm, hs, g, hg⟩
    exact ⟨hm, hs, g, fun x => congrArg Subtype.val (hg x)⟩

def parkerStandardAutomorphisms : Subgroup (Equiv.Perm ParkerLoop) where
  carrier := IsStandard
  one_mem' := by
    apply (isStandard_iff _).mpr
    refine ⟨fun _ _ => rfl, fun _ => rfl, 1, ?_⟩
    intro x
    exact (parkerCodeEquiv_one x.1).symm
  mul_mem' := by
    intro e f he hf
    rcases (isStandard_iff e).mp he with ⟨he, hse, g, hge⟩
    rcases (isStandard_iff f).mp hf with ⟨hf, hsf, h, hhf⟩
    apply (isStandard_iff _).mpr
    refine ⟨?_, ?_, g * h, ?_⟩
    · intro x y
      change e (f (parkerLoopMultiply x y)) = _
      rw [hf, he]
      rfl
    · intro s
      change e (f (0, s)) = _
      rw [hsf, hse]
    · intro x
      change (e (f x)).1 = _
      rw [hge, hhf, parkerCodeEquiv_mul]
  inv_mem' := by
    intro e he
    rcases (isStandard_iff e).mp he with ⟨he, hs, g, hg⟩
    apply (isStandard_iff _).mpr
    refine ⟨?_, ?_, g⁻¹, ?_⟩
    · intro x y
      apply e.injective
      change e (e.symm (parkerLoopMultiply x y)) =
        e (parkerLoopMultiply (e.symm x) (e.symm y))
      rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply]
    · intro s
      apply e.injective
      change e (e.symm (0, s)) = e (0, s)
      rw [e.apply_symm_apply, hs]
    · intro x
      have hh := hg (e.symm x)
      rw [e.apply_symm_apply] at hh
      have hi := congrArg (parkerCodeEquiv g⁻¹) hh
      rw [← parkerCodeEquiv_mul, inv_mul_cancel, parkerCodeEquiv_one] at hi
      exact hi.symm

abbrev ParkerStandardGroup := parkerStandardAutomorphisms

noncomputable def parkerStandardInduced (e : ParkerStandardGroup) : Mathieu24CodeModel :=
  Classical.choose ((isStandard_iff e.val).mp e.property).2.2

theorem parkerStandardInduced_spec (e : ParkerStandardGroup) (x : ParkerLoop) :
    (e.val x).1 = parkerCodeEquiv (parkerStandardInduced e) x.1 :=
  Classical.choose_spec ((isStandard_iff e.val).mp e.property).2.2 x

noncomputable def parkerStandardProjection : ParkerStandardGroup →* Mathieu24CodeModel where
  toFun := parkerStandardInduced
  map_one' := by
    apply parkerCodeEquiv_faithful
    intro a
    exact (parkerStandardInduced_spec 1 (a, 0)).symm
  map_mul' e f := by
    apply parkerCodeEquiv_faithful
    intro a
    calc
      parkerCodeEquiv (parkerStandardInduced (e * f)) a =
          ((e * f).val (a, 0)).1 := (parkerStandardInduced_spec (e * f) (a, 0)).symm
      _ = parkerCodeEquiv (parkerStandardInduced e) (f.val (a, 0)).1 :=
        parkerStandardInduced_spec e (f.val (a, 0))
      _ = parkerCodeEquiv (parkerStandardInduced e)
          (parkerCodeEquiv (parkerStandardInduced f) a) := by
        rw [parkerStandardInduced_spec f (a, 0)]
      _ = parkerCodeEquiv (parkerStandardInduced e * parkerStandardInduced f) a :=
        (parkerCodeEquiv_mul _ _ a).symm

theorem parkerStandardProjection_spec (e : ParkerStandardGroup) (x : ParkerLoop) :
    (e.val x).1 = parkerCodeEquiv (parkerStandardProjection e) x.1 :=
  parkerStandardInduced_spec e x

theorem parkerStandardGroup_finite : Finite ParkerStandardGroup := inferInstance

end Sporadic.Monster.Construction.TrialitySpin

namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes

theorem parkerStandard_preserves_sign (e : ParkerStandardGroup) (s : Bit) (x : ParkerLoop) :
    e.val (parkerSign s x) = parkerSign s (e.val x) := by
  have hx : parkerSign s x = parkerLoopMultiply x (0, s) := by
    simp [parkerSign, parkerLoopMultiply, parkerMultiply]
  rw [hx, e.property.1, e.property.2.1]
  simp [parkerSign, parkerLoopMultiply, parkerMultiply]

theorem parkerCodeEquiv_golayOne (g : Mathieu24CodeModel) :
    parkerCodeEquiv g golayOne = golayOne := by
  apply Subtype.ext
  rfl

theorem parkerStandard_omega_first (e : ParkerStandardGroup) :
    (e.val parkerOmega).1 = golayOne := by
  rw [parkerStandardProjection_spec]
  exact parkerCodeEquiv_golayOne _

theorem parkerStandard_omega (e : ParkerStandardGroup) :
    e.val parkerOmega = parkerSign (e.val parkerOmega).2 parkerOmega := by
  apply Prod.ext
  · exact parkerStandard_omega_first e
  · change (e.val parkerOmega).2 = 0 + (e.val parkerOmega).2
    simp

noncomputable def parkerStandardParity : ParkerStandardGroup →* Multiplicative Bit where
  toFun e := Multiplicative.ofAdd (e.val parkerOmega).2
  map_one' := rfl
  map_mul' e f := by
    change Multiplicative.ofAdd (e.val (f.val parkerOmega)).2 =
      Multiplicative.ofAdd ((e.val parkerOmega).2 + (f.val parkerOmega).2)
    rw [parkerStandard_omega f, parkerStandard_preserves_sign]
    simp [parkerSign, parkerOmega]

noncomputable def parkerStandardPlus : Subgroup ParkerStandardGroup := parkerStandardParity.ker

theorem parkerStandardPlus_iff (e : ParkerStandardGroup) :
    e ∈ parkerStandardPlus ↔ e.val parkerOmega = parkerOmega := by
  change (e.val parkerOmega).2 = 0 ↔ _
  constructor
  · intro h
    rw [parkerStandard_omega e, h, parkerSign_zero]
  · intro h
    exact congrArg Prod.snd h

theorem cocodeParity_coordinate (p : Omega) :
    cocodeParity (Submodule.Quotient.mk (Pi.single p (1 : Bit) : BinaryWord)) = 1 := by
  rw [cocodeParity_mk]
  simp [binaryDot_apply, allOnes, Pi.single_apply]

theorem cocodeParity_surjective : Function.Surjective cocodeParity := by
  intro s
  have hs : ∀ r : Bit, r = 0 ∨ r = 1 := by decide
  rcases hs s with rfl | rfl
  · exact ⟨0, map_zero _⟩
  · exact ⟨Submodule.Quotient.mk (Pi.single (Classical.arbitrary Omega) (1 : Bit) : BinaryWord),
      cocodeParity_coordinate _⟩

end Sporadic.Monster.Construction.TrialitySpin
