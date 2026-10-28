module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Sieve
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Classification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.StarKernel
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.CentralAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.SmallRows
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.HigherRows
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient

/-!
# Lifting the model of the actual star component

The original component maps onto a nontrivial simple component of
I/O_{3′}(I), with kernel exactly its two-group center. Descend the actual
fixed action through that kernel, apply the model sieve to its image, and
use the outer actor on A₆ together with full 1.1.5 to recover an original
carrier. The mixed adapter constructs the Sylow action from the realized
factors and retains literal conjugation on both subgroup levels.

The small and higher row theorems exhaust the full F.6.18 alternatives in
both source labelings. Thus the mixed setup supplies an intrinsic model
for every original component, without an additional catalogue or covering
premise. The universal F.6.18 implication and the genuine earlier 1.1.5
normalization, faithfulness and model/action conclusions remain explicit
source inputs. `Assembly.false_of_component_model` consumes this result;
the subsequent component-branch contradiction belongs to its parent.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.11 and
F.6.18, printed pp.306–310; 1.1.5, pp.501–503; 15.4.18, pp.1162–1163.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting
open MixedLocal AlternatingLocals.RawQuotient FFBranch.ClassificationComparison
open Chapter15.Section03.Candidates.ComponentStructure

/-- Lift an intrinsic model of the literal star image to a model of the
original component, using the original action and all 1.1.5 alternatives. -/
theorem intrinsicModel_of_star_model
    {I A : Type*} [Group I] [Finite I] [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (L : Subgroup I) (hL : IsComponent I L)
    (hodd : pPrimeCore 2 I = ⊥) (hs : Group.IsSolvable (pPrimeCore 3 I))
    (d : FixedAction L A) (hA : Nat.card A = 4)
    (h115 : ∀ a : A, a ≠ 1 → ModelAction115 L (d.action a))
    (model : IntrinsicComponentModel (starImage L)) : IntrinsicComponentModel L := by
  let := hL.2
  let : Group.IsPerfect (starImage L) :=
    Group.IsPerfect.map (QuotientGroup.mk' (pPrimeCore 3 I))
  let e := centralQuotientEquivStar L hL hodd hs
  let f := (quotientFixedAction d (component_center_eq_twoCore L hL hodd)).transport e
  obtain ⟨⟨a⟩, _⟩ := f.select_alternatingSix hA model
  exact model_of_quotient_alternating d hA h115 (e.trans a)

variable {G : Type*} [Group G] [Finite G]

/-- Actual mixed-setup application of the lifting argument. The extra model
premise concerns only the simple image; it is not a carrier identification of L. -/
theorem mixed_intrinsicModel_of_star_model
    {K : GroupClass} (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (L : Subgroup (generated T Y F)) (hL : IsComponent (generated T Y F) L)
    (hn : mixedZ T Y F ≤ normalizer (L : Set (generated T Y F)))
    (hfaithful : mixedZ T Y F ⊓ centralizer (L : Set (generated T Y F)) = ⊥)
    (hc : ∀ z : mixedZ T Y F, z ≠ 1 →
      HasCharacteristicTwo (centralizer ({(z : generated T Y F)} : Set (generated T Y F))))
    (h115 : ∀ z : mixedZ T Y F, z ≠ 1 → HasModelAction115 L (z : G))
    (model : IntrinsicComponentModel (starImage L)) : IntrinsicComponentModel L := by
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
    have hsU : (s : G) ∈ stabilizer T F := hS ▸ mem_map_of_mem I.subtype hs
    exact (((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) (z : G)).mp hz).2.2
      s hsU.1).symm
  obtain ⟨a, _, heval⟩ := exists_fixedAction_of_component L (mixedZ T Y F)
    hL S hn hfaithful hSZ hc
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (mixedZ T Y F) := IsElementaryAbelian.subgroupOf hZI
  have hfour : Nat.card (mixedZ T Y F) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZI).toEquiv).trans hZ
  have hact (z : mixedZ T Y F) (hz : z ≠ 1) : ModelAction115 L (a.action z) := by
    obtain ⟨α, hα, hm⟩ := h115 z hz
    have he : α = a.action z := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact (hα x).trans (congrArg Subtype.val (heval z x)).symm
    simpa only [he] using hm
  exact intrinsicModel_of_star_model L hL hodd
    (f611Conclusion_of_goldschmidt c.goldschmidt).core_solvable a hfour hact model

/-- The full source rows and F.6.11 hold for the literal quotient, and the
original component has a nontrivial simple image there. These supply the
row-by-row model extraction, with no extra classification. -/
theorem mixed_star_classification
    {K : GroupClass} (source : F618Universal K)
    (T : Sylow 2 G) {Y X M₂ : Subgroup G} {F : Bool → Subgroup G}
    (c : Configuration K T Y X M₂ F)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (L : Subgroup (generated T Y F)) (hL : IsComponent (generated T Y F) L) :
    let A := (firstGroup T Y F).subgroupOf (generated T Y F)
    let B := (secondGroup T F).subgroupOf (generated T Y F)
    F611Conclusion A B ∧
      GoldschmidtAlternatives.Remaining (threePrimeImage A) (threePrimeImage B) ∧
      pCore 2 ((generated T Y F) ⧸ pPrimeCore 3 (generated T Y F)) = ⊥ ∧
      IsComponent ((generated T Y F) ⧸ pPrimeCore 3 (generated T Y F)) (starImage L) ∧
      IsSimpleGroup (starImage L) := by
  obtain ⟨h611, hrows⟩ := mixed_classification_rows source T c
  exact ⟨h611, hrows, c.goldschmidt.primeToThreeCore_quotient_twoCore_eq_bot,
    star_isComponent_and_simple L hL hodd h611.core_solvable⟩

private theorem intrinsicModel_of_remainingOrdered
    {D : Type*} [Group D] [Finite D] {A B Q : Subgroup D}
    (hQ : IsComponent D Q) (hsimple : IsSimpleGroup Q) (hcore : pCore 2 D = ⊥)
    (hrows : GoldschmidtAlternatives.RemainingOrdered A B) :
    IntrinsicComponentModel Q := by
  have h : SmallRows.Selected A B ∨
      (GoldschmidtAlternatives.Case10 A B ∨ GoldschmidtAlternatives.Case11 A B ∨
        GoldschmidtAlternatives.Case12 A B ∨ GoldschmidtAlternatives.Case13 A B) := by
    simpa only [SmallRows.Selected, GoldschmidtAlternatives.RemainingOrdered, or_assoc]
      using hrows
  exact h.elim (SmallRows.model hQ hsimple hcore) (HigherRows.intrinsicModel hQ hsimple hcore)

/-- Every surviving F.6.18 row gives an actual intrinsic component model,
in either source labeling. The solvable row (2) is excluded by SmallRows. -/
theorem intrinsicModel_of_remaining
    {D : Type*} [Group D] [Finite D] {A B Q : Subgroup D}
    (hQ : IsComponent D Q) (hsimple : IsSimpleGroup Q) (hcore : pCore 2 D = ⊥)
    (hrows : GoldschmidtAlternatives.Remaining A B) : IntrinsicComponentModel Q := by
  rcases hrows with hrows | hrows
  · exact intrinsicModel_of_remainingOrdered hQ hsimple hcore hrows
  · exact intrinsicModel_of_remainingOrdered hQ hsimple hcore hrows

/-- Exhaustive model extraction for the actual image in I/O_{3′}(I).
F.6.11, nontriviality, simplicity and the quotient two-core condition are
all discharged from the mixed setup and the original component. -/
theorem mixed_star_intrinsicModel
    {K : GroupClass} (source : F618Universal K)
    (T : Sylow 2 G) {Y X M₂ : Subgroup G} {F : Bool → Subgroup G}
    (c : Configuration K T Y X M₂ F)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (L : Subgroup (generated T Y F)) (hL : IsComponent (generated T Y F) L) :
    IntrinsicComponentModel (starImage L) := by
  obtain ⟨_, hrows, hcore, hcomp, hsimple⟩ := mixed_star_classification source T c hodd L hL
  exact intrinsicModel_of_remaining hcomp hsimple hcore hrows

/-- The original component has an intrinsic model under the genuine mixed
setup and earlier 1.1.5 conclusions. The star-image model and its central
covering kernel are proved internally; no later component identification
or branch impossibility is assumed. -/
theorem mixed_intrinsicModel
    {K : GroupClass} (source : F618Universal K)
    (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (L : Subgroup (generated T Y F)) (hL : IsComponent (generated T Y F) L)
    (hn : mixedZ T Y F ≤ normalizer (L : Set (generated T Y F)))
    (hfaithful : mixedZ T Y F ⊓ centralizer (L : Set (generated T Y F)) = ⊥)
    (hc : ∀ z : mixedZ T Y F, z ≠ 1 →
      HasCharacteristicTwo (centralizer ({(z : generated T Y F)} : Set (generated T Y F))))
    (h115 : ∀ z : mixedZ T Y F, z ≠ 1 → HasModelAction115 L (z : G)) :
    IntrinsicComponentModel L := by
  exact mixed_intrinsicModel_of_star_model T d c hZ hodd L hL hn hfaithful hc h115
    (mixed_star_intrinsicModel source T c hodd L hL)

/-- The non-two-core generalized-Fitting branch supplies an original component
and its model. Only the authorized earlier source conclusions remain as inputs;
the parent can apply `false_of_component_model` to this same component. -/
theorem exists_mixed_component_model
    {K : GroupClass} (source : F618Universal K)
    (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (hne : generalizedFitting (generated T Y F) ≠ pCore 2 (generated T Y F))
    (ha : ∀ L : Subgroup (generated T Y F), IsComponent (generated T Y F) L →
      mixedZ T Y F ≤ normalizer (L : Set (generated T Y F)) ∧
        mixedZ T Y F ⊓ centralizer (L : Set (generated T Y F)) = ⊥)
    (hc : ∀ z : mixedZ T Y F, z ≠ 1 →
      HasCharacteristicTwo (centralizer ({(z : generated T Y F)} : Set (generated T Y F))))
    (h115 : ∀ L : Subgroup (generated T Y F), IsComponent (generated T Y F) L →
      ∀ z : mixedZ T Y F, z ≠ 1 → HasModelAction115 L (z : G)) :
    ∃ L : Subgroup (generated T Y F), IsComponent (generated T Y F) L ∧
      IntrinsicComponentModel L := by
  obtain ⟨L, hL⟩ := exists_component_of_generalizedFitting_ne hodd hne
  exact ⟨L, hL, mixed_intrinsicModel source T d c hZ hodd L hL
    (ha L hL).1 (ha L hL).2 hc (h115 L hL)⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting
