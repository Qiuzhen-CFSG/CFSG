module

public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents.FactorModels

/-!
# Intrinsic star components and their ambient conjugacy orbits

For N normal in X, a quasisimple F*(N) is an intrinsic C-component with
one X-conjugate, even when N is a proper symmetric or G₂(2) extension.
For an actual product N ≃ D × E with the B.5.6 factor models, the canonical
candidates are the two embedded solvable residuals. Every C-component is
one of these candidates, so X can only permute their two ambient images.
The nontrivial candidates are identified by actual multiplicative
equivalences with the perfect linear models or A₅. If both vanish, the
result returns actual S₃ equivalences for both original factors.

The hyperplane case selects the first SL₃(2) factor. Its second factor is
supplied by `HyperplaneSecondCase.factorModel`. These intrinsic results
feed `ComponentExistence.exists_of_star_component` after the parent
supplies the model's cubic witness; no outside placement or component
generation of the original span is asserted here.

Source: Aschbacher–Smith B.5.1, printed pp.99–103, B.5.5–6, pp.104–105,
and the proof of 15.3.49(i), pp.1143–1144, combined manuscript 1 March 2004.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
variable {X D E : Type*} [Group X] [Group D] [Group E]

/-- The first actual residual factor, transported into N by the specified product equivalence. -/
def left (N : Subgroup X) (e : N ≃* D × E) : Subgroup N :=
  ((solvableResidual D).prod (⊥ : Subgroup E)).map e.symm.toMonoidHom

/-- The second actual residual factor. It may be trivial in the degree-one SL₂ case. -/
def right (N : Subgroup X) (e : N ≃* D × E) : Subgroup N :=
  ((⊥ : Subgroup D).prod (solvableResidual E)).map e.symm.toMonoidHom

/-- Each canonical factor is normal inside N; only the pair must be ambient invariant. -/
theorem left_normal (N : Subgroup X) (e : N ≃* D × E) : (left N e).Normal :=
  (inferInstance : ((solvableResidual D).prod (⊥ : Subgroup E)).Normal).map _ e.symm.surjective

theorem right_normal (N : Subgroup X) (e : N ≃* D × E) : (right N e).Normal :=
  (inferInstance : ((⊥ : Subgroup D).prod (solvableResidual E)).Normal).map _ e.symm.surjective

noncomputable def leftEquiv (N : Subgroup X) (e : N ≃* D × E) :
    left N e ≃* solvableResidual D :=
  (e.symm.subgroupMap _).symm.trans residualLeftEquiv

noncomputable def rightEquiv (N : Subgroup X) (e : N ≃* D × E) :
    right N e ≃* solvableResidual E :=
  (e.symm.subgroupMap _).symm.trans residualRightEquiv

theorem left_component (N : Subgroup X) (e : N ≃* D × E)
    (h : IsQuasisimple (solvableResidual D)) :
    (left N e).IsCComponent ∧ IsQuasisimple (left N e) := by
  have hh := (residualLeft_component (E := E) h).map_equiv e.symm
  exact ⟨hh.isCComponent, hh.2⟩

theorem right_component (N : Subgroup X) (e : N ≃* D × E)
    (h : IsQuasisimple (solvableResidual E)) :
    (right N e).IsCComponent ∧ IsQuasisimple (right N e) := by
  have hh := (residualRight_component (D := D) h).map_equiv e.symm
  exact ⟨hh.isCComponent, hh.2⟩

theorem component_eq_left_or_right (N : Subgroup X) (e : N ≃* D × E)
    (hD : solvableResidual D = ⊥ ∨ IsQuasisimple (solvableResidual D))
    (hE : solvableResidual E = ⊥ ∨ IsQuasisimple (solvableResidual E))
    {B : Subgroup N} (hB : B.IsCComponent) : B = left N e ∨ B = right N e := by
  rcases cComponent_eq_residual_factor hD hE (hB.map_equiv e) with h | h
  · left
    have hh := congrArg (map e.symm.toMonoidHom) h
    simpa [Subgroup.map_map, left] using hh
  · right
    have hh := congrArg (map e.symm.toMonoidHom) h
    simpa [Subgroup.map_map, right] using hh


/-- Literal inclusion of the generalized Fitting subgroup into the ambient group. -/
noncomputable def generalizedFittingInEquiv (N : Subgroup X) :
    (generalizedFitting N).map N.subtype ≃* generalizedFitting N :=
  ((generalizedFitting N).equivMapOfInjective N.subtype N.subtype_injective).symm

/-- The intrinsic quasisimple F*(N) is a C-component even for proper extensions N.
Its ambient image is normal, so its conjugacy orbit has exactly one member. -/
theorem generalizedFitting_component (N : Subgroup X) [N.Normal]
    (h : IsQuasisimple (generalizedFitting N)) :
    (generalizedFitting N).IsCComponent ∧
    (generalizedFitting N).map N.subtype ≤ N ∧
    IsQuasisimple ((generalizedFitting N).map N.subtype) ∧
    (Set.range fun x : X =>
      ((generalizedFitting N).map N.subtype).map (MulAut.conj x).toMonoidHom).ncard = 1 := by
  let := h
  exact ⟨generalizedFitting_isCComponent N, map_subtype_le _,
    IsQuasisimple.of_mulEquiv (generalizedFittingInEquiv N).symm,
    generalizedFitting_normal_orbit N⟩

variable [Finite X]

private theorem finite_factors (N : Subgroup X) (e : N ≃* D × E) :
    Finite D ∧ Finite E := by
  let : Finite (D × E) := Finite.of_equiv N e.toEquiv
  exact ⟨Finite.of_surjective (Prod.fst : D × E → D) Prod.fst_surjective,
    Finite.of_surjective (Prod.snd : D × E → E) Prod.snd_surjective⟩

/-- Both canonical factors have their actual model identifications whenever nontrivial. -/
theorem canonical_factors (N : Subgroup X) (e : N ≃* D × E)
    (hD : FFAlternatives.FactorModel D) (hE : FFAlternatives.FactorModel E) :
    ((left N e = ⊥ ∧ Nonempty (D ≃* Equiv.Perm (Fin 3))) ∨
      ((left N e).IsCComponent ∧ IsQuasisimple (left N e) ∧ ComponentModel (left N e))) ∧
    ((right N e = ⊥ ∧ Nonempty (E ≃* Equiv.Perm (Fin 3))) ∨
      ((right N e).IsCComponent ∧ IsQuasisimple (right N e) ∧ ComponentModel (right N e))) := by
  obtain ⟨hfinD, hfinE⟩ := finite_factors N e
  let := hfinD
  let := hfinE
  constructor
  · rcases factor_residual hD with ⟨hf, hb⟩ | ⟨hq, hm⟩
    · exact Or.inl ⟨by simp [left, hb], hf⟩
    · exact Or.inr ⟨(left_component N e hq).1, (left_component N e hq).2,
        hm.of_equiv (leftEquiv N e)⟩
  · rcases factor_residual hE with ⟨hf, hb⟩ | ⟨hq, hm⟩
    · exact Or.inl ⟨by simp [right, hb], hf⟩
    · exact Or.inr ⟨(right_component N e hq).1, (right_component N e hq).2,
        hm.of_equiv (rightEquiv N e)⟩

/-- Every C-component belongs to the explicitly embedded residual pair. -/
theorem all_components (N : Subgroup X) (e : N ≃* D × E)
    (hD : FFAlternatives.FactorModel D) (hE : FFAlternatives.FactorModel E)
    {B : Subgroup N} (hB : B.IsCComponent) : B = left N e ∨ B = right N e := by
  obtain ⟨hfinD, hfinE⟩ := finite_factors N e
  let := hfinD
  let := hfinE
  apply component_eq_left_or_right N e _ _ hB
  · exact (factor_residual hD).elim (fun h => Or.inl h.2) (fun h => Or.inr h.1)
  · exact (factor_residual hE).elim (fun h => Or.inl h.2) (fun h => Or.inr h.1)

/-- Every ambient conjugate of a component is one of the two specified images. -/
theorem conjugate_eq_left_or_right (N : Subgroup X) [N.Normal] (e : N ≃* D × E)
    (hD : FFAlternatives.FactorModel D) (hE : FFAlternatives.FactorModel E)
    {B : Subgroup N} (hB : B.IsCComponent) (x : X) :
    (B.map N.subtype).map (MulAut.conj x).toMonoidHom = (left N e).map N.subtype ∨
    (B.map N.subtype).map (MulAut.conj x).toMonoidHom = (right N e).map N.subtype :=
  normal_cComponent_conjugates_pair N (left N e) (right N e)
    (fun _ h => all_components N e hD hE h) hB x

/-- The pair controls conjugacy in the original ambient group, not only inside N. -/
theorem orbit_le_two (N : Subgroup X) [N.Normal] (e : N ≃* D × E)
    (hD : FFAlternatives.FactorModel D) (hE : FFAlternatives.FactorModel E)
    {B : Subgroup N} (hB : B.IsCComponent) :
    (Set.range fun x : X => (B.map N.subtype).map (MulAut.conj x).toMonoidHom).ncard ≤ 2 :=
  normal_cComponent_orbit_le_two N (left N e) (right N e)
    (fun _ h => all_components N e hD hE h) hB

/-- Exhaust the product alternatives, returning actual S₃ equivalences in the
exceptional case and an explicitly modeled quasisimple C-component otherwise. -/
theorem exists_component_or_symmetric_three_pair (N : Subgroup X) [N.Normal]
    (e : N ≃* D × E) (hD : FFAlternatives.FactorModel D) (hE : FFAlternatives.FactorModel E) :
    (Nonempty (D ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (E ≃* Equiv.Perm (Fin 3))) ∨
    ∃ B : Subgroup N, (B = left N e ∨ B = right N e) ∧ B.IsCComponent ∧
      IsQuasisimple B ∧ ComponentModel B ∧
      (Set.range fun x : X => (B.map N.subtype).map (MulAut.conj x).toMonoidHom).ncard ≤ 2 := by
  obtain ⟨hleft, hright⟩ := canonical_factors N e hD hE
  rcases hleft with ⟨_, hd⟩ | ⟨hc, hq, hm⟩
  · rcases hright with ⟨_, he⟩ | ⟨hc, hq, hm⟩
    · exact Or.inl ⟨hd, he⟩
    · exact Or.inr ⟨right N e, Or.inr rfl, hc, hq, hm, orbit_le_two N e hD hE hc⟩
  · exact Or.inr ⟨left N e, Or.inl rfl, hc, hq, hm, orbit_le_two N e hD hE hc⟩

/-- The same construction with the exceptional all-solvable case excluded. -/
theorem exists_component (N : Subgroup X) [N.Normal] (e : N ≃* D × E)
    (hD : FFAlternatives.FactorModel D) (hE : FFAlternatives.FactorModel E)
    (hne : ¬ (Nonempty (D ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (E ≃* Equiv.Perm (Fin 3)))) :
    ∃ B : Subgroup N, B.IsCComponent ∧ IsQuasisimple B ∧ ComponentModel B ∧
      (Set.range fun x : X => (B.map N.subtype).map (MulAut.conj x).toMonoidHom).ncard ≤ 2 := by
  obtain ⟨B, _, hB⟩ := (exists_component_or_symmetric_three_pair N e hD hE).resolve_left hne
  exact ⟨B, hB⟩


/-- A quasisimple first factor selects the left component without testing the
second factor for solvability. -/
theorem exists_component_of_quasisimple_left [IsQuasisimple D]
    (N : Subgroup X) [N.Normal] (e : N ≃* D × E)
    (hD : FFAlternatives.FactorModel D) (hE : FFAlternatives.FactorModel E) :
    (left N e).IsCComponent ∧ IsQuasisimple (left N e) ∧ ComponentModel (left N e) ∧
      (Set.range fun x : X =>
        ((left N e).map N.subtype).map (MulAut.conj x).toMonoidHom).ncard ≤ 2 := by
  let er : solvableResidual D ≃* D :=
    (MulEquiv.subgroupCongr solvableResidual_eq_top).trans topEquiv
  have hq := IsQuasisimple.of_mulEquiv er.symm
  have hc := left_component N e hq
  obtain ⟨hl, _⟩ := canonical_factors N e hD hE
  rcases hl with ⟨hb, _⟩ | ⟨_, _, hm⟩
  · exact (hc.1.ne_bot hb).elim
  · exact ⟨hc.1, hc.2, hm, orbit_le_two N e hD hE hc.1⟩

/-- B.5.6(5) is covered by its first SL₃(2) factor. The caller obtains the
second model from `HyperplaneSecondCase.factorModel`. -/
theorem hyperplane_first_component (N : Subgroup X) [N.Normal] (e : N ≃* D × E)
    (eD : D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hE : FFAlternatives.FactorModel E) :
    (left N e).IsCComponent ∧ IsQuasisimple (left N e) ∧ ComponentModel (left N e) ∧
      (Set.range fun x : X =>
        ((left N e).map N.subtype).map (MulAut.conj x).toMonoidHom).ncard ≤ 2 := by
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv eD.symm
  exact exists_component_of_quasisimple_left N e
    (.linearThree FFAlternatives.BinaryField.two (by decide) eD) hE

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents
