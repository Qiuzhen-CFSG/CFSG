module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.FactorCommutation
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.ComponentInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Assembly

/-!
# Source component contradiction without premature factor commutation

The actual mixed component action comes from full ABC and the original local
hypotheses. Its intrinsic model selects A6 and the S6 star extension. Only then
does the proved local recognition identify the first factor as A4, making its
four-group the actual two-core. The source pair now supplies factor commutation
and the existing incompatible two-rank bounds give the contradiction.

Source: Aschbacher--Smith, proof of 15.4.18, p.1163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure LocalSetup LocalSetup.SourceWitnesses
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open LocalSetup.TwoFactors.ComponentBranch
open LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The recognized component forces commutation before applying the rank contradiction. -/
theorem source_selected_component_contradiction {κ : GroupClass.{u}} {T : Sylow 2 G}
    {M₁ M₂ Y X : Subgroup G} (hY : Input κ T M₁ Y 1) (hX : Input κ T M₂ X 2)
    (p : Pair T M₂ X)
    (d : RealizedFactors T Y X M₁ M₂ p.quotient.factor)
    (c : Configuration κ T Y X M₂ p.quotient.factor)
    (L : Subgroup (generated T Y p.quotient.factor))
    (hL : IsComponent (generated T Y p.quotient.factor) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : mixedZ T Y p.quotient.factor ⊓
      centralizer (L : Set (generated T Y p.quotient.factor)) = ⊥)
    (eSelected : selectedJoin L (mixedZ T Y p.quotient.factor) ≃* Equiv.Perm (Fin 6)) : False := by
  have hYP : IsPPerfect 2 Y := YFamily.perfect hY.member
  have hFP : IsPPerfect 2 (p.quotient.factor false) := p.quotient.factor_perfect false
  obtain ⟨_,⟨eF⟩⟩ := AlternatingLocals.Mixed.factors_alternating_four
    T d c L hL eL hZ hfaithful eSelected hYP hFP
  have hcard : Nat.card (p.quotient.factor false) = 12 := by
    rw [Nat.card_congr eF.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  exact false_of_selected_component T d c (p.source_commute_of_factor_card hX hcard)
    hYP hFP L hL eL hZ hfaithful eSelected

/-- Full earlier ABC supplies the component action; the actual model then contradicts it. -/
theorem source_component_model_contradiction {κ : GroupClass.{u}}
    (hABC : ∀ (A : Type u) [Group A] [Finite A], ChapterA.Section02.TheoremsABC κ A)
    {T : Sylow 2 G} {M₁ M₂ Y X : Subgroup G}
    (hY : Input κ T M₁ Y 1) (hX : Input κ T M₂ X 2) (p : Pair T M₂ X)
    (d : RealizedFactors T Y X M₁ M₂ p.quotient.factor)
    (c : Configuration κ T Y X M₂ p.quotient.factor)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (L : Subgroup (generated T Y p.quotient.factor))
    (hL : IsComponent (generated T Y p.quotient.factor) L)
    (model : IntrinsicComponentModel L) : False := by
  let F := p.quotient.factor
  let I := generated T Y F
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨_,hc,hinputs⟩ := source_mixed_component_inputs hABC hY c
  obtain ⟨⟨hn,hfaithful⟩,_⟩ := hinputs L hL
  have hZU : Z ≤ stabilizer T F :=
    ((centralOmega_le_thompsonAlpha _).trans (alpha_le_baumann _)).trans
      (le_inf inf_le_left d.baumann_invariant)
  have hZI : Z ≤ I := hZU.trans (le_sup_right.trans le_sup_left)
  obtain ⟨S,hS⟩ := c.generated_sylow
  have hSZ : (S : Subgroup I) ≤ centralizer (mixedZ T Y F : Set I) := by
    intro s hs z hz
    apply Subtype.ext
    have hsU : (s : G) ∈ stabilizer T F := hS ▸ mem_map_of_mem I.subtype hs
    exact (((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) (z : G)).mp hz).2.2
      s hsU.1).symm
  obtain ⟨a,_,heval⟩ := exists_fixedAction_of_component L (mixedZ T Y F)
    hL S hn hfaithful hSZ hc
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (mixedZ T Y F) := IsElementaryAbelian.subgroupOf hZI
  have hfour : Nat.card (mixedZ T Y F) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZI).toEquiv).trans hZ
  let : IsQuasisimple L := hL.2
  obtain ⟨⟨eL⟩,⟨eS⟩⟩ := a.select_alternatingSix hfour model
  obtain ⟨eStar⟩ := selected_join_equiv_innerExtension c.sqtk.stronglyQuasithin
    L (mixedZ T Y F) hL eL a.action heval
  exact source_selected_component_contradiction hY hX p d c L hL eL hZ hfaithful (eStar.trans eS)

end CFSG.Quasithin.Chapter15.Section04.InitialSource
