module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Sieve
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.StarTransport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Selected

/-!
# Assembly after intrinsic component lifting

The raw mixed setup provides a Sylow subgroup of I and its central four-group.
The genuine 1.1.5 normalization and faithfulness clauses construct the action
on a component; subnormal inheritance supplies its characteristic-two fixed
subgroups. The intrinsic model sieve constructs A₆ and S₆. Transport through
the literal star quotient then supplies the selected case to the local
recognition, invariance and rank contradiction.

The only additional mathematical premise here is `IntrinsicComponentModel`
for the original component. Deriving it from every F.6.18 quotient row and
all 1.1.5 alternatives remains an independent lifting obligation. These are
conditional assembly theorems, not a completion of the raw component branch
or of 15.4.18. The F.6.18 application is supplied separately in `Classification`.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
open MixedLocal AlternatingLocals.RawQuotient
variable {G : Type*} [Group G] [Finite G]

/-- Once the original component's model has been extracted from the source
classifications, its faithful action, both selected models, all local structure,
and the incompatible rank bounds are constructed from the raw configuration. -/
theorem false_of_component_model
    {K : GroupClass} (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (hcomm : F false ≤ centralizer (F true : Set G))
    (hY : IsPPerfect 2 Y) (hF : IsPPerfect 2 (F false))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (L : Subgroup (generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (generated T Y F) L)
    (hn : mixedZ T Y F ≤ normalizer (L : Set (generated T Y F)))
    (hfaithful : mixedZ T Y F ⊓ centralizer (L : Set (generated T Y F)) = ⊥)
    (hc : ∀ z : mixedZ T Y F, z ≠ 1 →
      HasCharacteristicTwo (centralizer ({(z : generated T Y F)} : Set (generated T Y F))))
    (model : IntrinsicComponentModel L) : False := by
  let I := generated T Y F
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hZU : Z ≤ stabilizer T F :=
    ((centralOmega_le_thompsonAlpha _).trans (alpha_le_baumann _)).trans
      (le_inf inf_le_left d.baumann_invariant)
  have hZI : Z ≤ I := hZU.trans (le_sup_right.trans le_sup_left)
  obtain ⟨S, hS⟩ := c.generated_sylow
  have hSZ : (S : Subgroup I) ≤ centralizer (mixedZ T Y F : Set I) := by
    intro s hs z hz
    apply Subtype.ext
    have hsU : (s : G) ∈ stabilizer T F :=
      hS ▸ Subgroup.mem_map_of_mem I.subtype hs
    exact (((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) (z : G)).mp hz).2.2
      s hsU.1).symm
  obtain ⟨a, _, heval⟩ := exists_fixedAction_of_component L (mixedZ T Y F)
    hL S hn hfaithful hSZ hc
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (mixedZ T Y F) := IsElementaryAbelian.subgroupOf hZI
  have hfour : Nat.card (mixedZ T Y F) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZI).toEquiv).trans hZ
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  obtain ⟨⟨eL⟩, ⟨eS⟩⟩ := a.select_alternatingSix hfour model
  obtain ⟨eStar⟩ := selected_join_equiv_innerExtension c.sqtk.stronglyQuasithin
    L (mixedZ T Y F) hL eL a.action heval
  exact false_of_selected_component T d c hcomm hY hF L hL eL hZ hfaithful (eStar.trans eS)

/-- Conditional final assembly, with the remaining model-lifting premise
explicit. This premise must be proved from the full F.6.18 quotient alternatives
and the genuine 1.1.5 conclusions before eliminating the raw source branch. -/
theorem generalizedFitting_eq_twoCore_of_component_models
    {K : GroupClass} (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (hcomm : F false ≤ centralizer (F true : Set G))
    (hY : IsPPerfect 2 Y) (hF : IsPPerfect 2 (F false))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (h115 : ∀ L : Subgroup (generated T Y F),
      Theory.GroupTheory.IsComponent (generated T Y F) L →
      mixedZ T Y F ≤ normalizer (L : Set (generated T Y F)) ∧
        mixedZ T Y F ⊓ centralizer (L : Set (generated T Y F)) = ⊥)
    (hc : ∀ z : mixedZ T Y F, z ≠ 1 →
      HasCharacteristicTwo (centralizer ({(z : generated T Y F)} : Set (generated T Y F))))
    (models : ∀ L : Subgroup (generated T Y F),
      Theory.GroupTheory.IsComponent (generated T Y F) L → IntrinsicComponentModel L) :
    Theory.GroupTheory.generalizedFitting (generated T Y F) = pCore 2 (generated T Y F) := by
  by_contra hne
  obtain ⟨L, hL⟩ := exists_component_of_generalizedFitting_ne hodd hne
  exact false_of_component_model T d c hcomm hY hF hZ L hL
    (h115 L hL).1 (h115 L hL).2 hc (models L hL)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
