module
public import CFSG.Quasithin.Chapter14.Section02.ProperComponent
public import CFSG.Quasithin.Chapter14.Section02.ProperOutsideSylow
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import CFSG.Quasithin.Chapter14.Section02.ProperCompletionThreeResidual

/-!
# The original triality completion residual

The binary triality field-action theorem identifies the canonical component
with the prime-to-three residual of the actual completion. Three-generation
of the literal source Y then yields Y≤L and LS=X, for every binary field
parameter, including two. This discharges the A.3.18 placement needed by
the larger-field triality Borel branch. Proper Sylow overgroup coverage
in that model remains a separate source calculation.

Source: Aschbacher--Smith A.3.18 and 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual source completion has the triality cubic residual, at every binary parameter. -/
theorem source_proper_completion_triality_three_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (_hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥)
    {n : ℕ} (hn : 0 < n) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L → IsSimpleGroup L → Triality.Standard.IsTrialityGroupAt (2^n) L →
      (primeToResidual 3 X).map X.subtype = L ∧ sourceResidual M Mc ≤ L ∧ L ⊔ S = X := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change IsQuasisimple L → IsSimpleGroup L → Triality.Standard.IsTrialityGroupAt (2^n) L →
      (primeToResidual 3 X).map X.subtype = L ∧ sourceResidual M Mc ≤ L ∧ L ⊔ S = X
  intro hq hsimple hmodel
  obtain ⟨eL⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L n hn).mp hmodel
  let := hq
  let := hsimple
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  let C := L.subgroupOf X
  let d := subgroupOfEquivOfLe hL.1
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv d.symm
  have hC : IsComponent X C := ⟨hL.2.subnormal,inferInstance⟩
  have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H hG hcorea
  let : IsSimpleGroup C := d.isSimpleGroup
  have hzC : center C = ⊥ := center_eq_bot_of_simple_perfect
  let eC : (C ⧸ center C) ≃* Triality.Standard.BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hzC).trans QuotientGroup.quotientBot).trans
      (d.trans eL)
  have hres : C = primeToResidual 3 X :=
    (Triality.Standard.CubicComponentAction.component_eq_primeClosure_and_residual
      (hsq.stronglyQuasithin 3 Nat.prime_three (by decide)) hC (by rw [hzC]; simp)
      n hn eC).2
  have he : (primeToResidual 3 X).map X.subtype = L := by
    rw [←hres,map_subgroupOf_eq_of_le hL.1]
  exact ⟨he,source_proper_completion_sylow_join_of_three_residual hG T hempty hM hu hmany
    hcard e K S hKL he⟩

end CFSG.Quasithin.Chapter14.Section02
