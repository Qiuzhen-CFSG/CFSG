module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleFixed
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers.Center

/-!
# The original paired terminal with the intrinsic Rudvalis center discharged

This is the literal proper-completion consumer of the actual triality and
Rudvalis fixed-group exclusions. The proved centerlessness of the concrete
Rudvalis model supplies the central-cover transport input internally. The
earlier-source placement and three-rank of the full paired residual remain
the precise independent inputs to the terminal.

Source: Aschbacher--Smith, 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The original proper-completion terminal uses intrinsic Rudvalis centerlessness. -/
theorem source_proper_quasisimple_pair_terminal_intrinsic
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
    (hZS : centralInvolutions T ≤ S)
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥)
    (hpair : (pResidual 2 H).map H.subtype ≤
      (solvableResidual (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G)).map
        (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G).subtype)
    (hr : 2 ≤ primeRank 3 ((pResidual 2 H).map H.subtype)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L → ¬ClassificationModels.IsBenderModel L ∧
      ∃ z : G, z ∈ centralInvolutions T ∧ orderOf z = 2 ∧
      L = ⁅L,zpowers z⁆ ∧ ¬L ≤ Mc ∧
      ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
        ModelAction115 L α ∧
        (∀ n : ℕ, 0 < n → Triality.Standard.IsTrialityGroupAt (2^n) L →
          α ∉ (MulAut.conj (G := L)).range) ∧
        (∀ _f : (L ⧸ pCore 2 L) ≃* Rudvalis.Model, ¬TwoCentralInner α) := by
  exact source_proper_quasisimple_pair_terminal hG T hempty hM hu hmany hcard e
    H hH K S hST hi hN hplacement hgen hK hSN hZS hcore hpair hr
    Rudvalis.LowCentralizers.model_center_eq_bot

end CFSG.Quasithin.Chapter14.Section02
