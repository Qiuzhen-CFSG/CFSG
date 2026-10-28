module
public import CFSG.Quasithin.Chapter14.Section02.ProperReeBorelExclusion
public import CFSG.Quasithin.Chapter14.Section02.ProperOutsideSylow
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual
public import CFSG.Quasithin.Chapter14.Section02.ProperCompletionThreeResidual

/-!
# The original Ree source residual and Borel contradiction

The cubic A.3.18 action calculation proves that the canonical completion
residual contains the literal source subgroup Y. Solvable full-Sylow
control in the Ree model then contradicts the factor of three in Y.
The simplicity premise is exactly that of the Lie-type case of 1.1.5;
the native model inherits all simple/perfect properties from L.

Source: Aschbacher--Smith A.3.18 and 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The complete Ree branch derives its earlier A.3.18 placement. -/
theorem source_proper_completion_ree_exclusion
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
    {m : ℕ} (hm : 1 ≤ m) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L → IsSimpleGroup L → Nonempty (L ≃* ReeF4.Model m) → False := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  let Y := sourceResidual M Mc
  change IsQuasisimple L → IsSimpleGroup L → Nonempty (L ≃* ReeF4.Model m) → False
  rintro hq hsimple ⟨eL⟩
  let := hq
  let := hsimple
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨hL,_,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  let C := L.subgroupOf X
  let d := subgroupOfEquivOfLe hL.1
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv d.symm
  have hC : IsComponent X C := ⟨hL.2.subnormal,inferInstance⟩
  have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H hG hcorea
  let : IsSimpleGroup C := d.isSimpleGroup
  have hzC : center C = ⊥ := center_eq_bot_of_simple_perfect
  let eC : (C ⧸ center C) ≃* ReeF4.Model m :=
    ((QuotientGroup.quotientMulEquivOfEq hzC).trans QuotientGroup.quotientBot).trans
      (d.trans eL)
  have hZC : IsPGroup 2 (center C) := hzC.symm ▸ IsPGroup.of_bot
  have hres : C = primeToResidual 3 X :=
    (ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual.component_eq_primeClosure_and_residual
      hsq hC hZC hm eC).2
  have hYX : Y ≤ X := le_sup_right.trans le_sup_left
  have hy := source_residual_three_generated hG T hempty hM hu hmany hcard e
  have hyX : primeToResidual 3 (Y.subgroupOf X) = ⊤ := by
    rw [←map_primeToResidual_of_surjective 3 (subgroupOfEquivOfLe hYX).symm.toMonoidHom
      (subgroupOfEquivOfLe hYX).symm.surjective,hy,←MonoidHom.range_eq_map]
    exact (subgroupOfEquivOfLe hYX).symm.range_eq_top
  have hYC : Y.subgroupOf X ≤ C := hres.symm ▸ le_primeToResidual_of_eq_top 3 _ hyX
  have hYL : Y ≤ L := by
    intro y hy
    exact hYC (show (⟨y,hYX hy⟩ : X) ∈ Y.subgroupOf X from hy)
  have hk : IsPGroup 2 eL.toMonoidHom.ker := by
    rw [eL.toMonoidHom.ker_eq_bot_iff.mpr eL.injective]
    exact IsPGroup.of_bot
  exact source_proper_completion_ree_borel_exclusion hG T hempty hM hu hmany
    hcard e H hH K S hST hi hN hplacement hcore hm hYL eL.toMonoidHom eL.surjective hk



/-- The root-data marking in the literal 1.1.5 Ree case. -/
theorem source_proper_completion_ree_model_exclusion
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
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥)
    {m : ℕ} (hm : 1 ≤ m) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L → IsSimpleGroup L → Chapter1.Section02.LocalModels.IsReeF4At L m → False := by
  dsimp only
  intro hq hs hmodel
  obtain ⟨d,⟨eL⟩⟩ := hmodel
  exact source_proper_completion_ree_exclusion hG T hempty hM hu hmany hcard e
    H hH K S hST hi hN hplacement hgen hK hSN hcore hm hq hs ⟨eL.trans d.modelEquiv⟩

end CFSG.Quasithin.Chapter14.Section02
