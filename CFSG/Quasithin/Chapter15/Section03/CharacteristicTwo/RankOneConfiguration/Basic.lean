module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Basic

/-!
# Minimal outside overgroups in the rank-one branch

Every intermediate subgroup containing the common Sylow subgroup contains
`O₂(I)`, and hence has nontrivial two-core. Minimality of `I` therefore
puts every proper intermediate overgroup of `Y₊S` in `M ∩ I`. Once the
component containment `Y₊ ≤ L` is proved, this also gives `I = LS`.

The component normality and containment arguments and the small-group
classification are separate obligations. The conditional conclusions here
do not assert those inputs or the identification of the action with `S₈`.
All normality statements are relative to the displayed overgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27(4) and 15.3.29, printed pp.1130–1132.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

open Subgroup

variable {G : Type*} [Group G]

/-- The exact input 15.3.26(3); the rank-one branch does not import the
rank-two elimination to obtain this assertion. -/
def SolvableInvariantControl (d : LocalData G) (I : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ I → Group.IsSolvable X →
    d.Yplus ⊔ d.S ≤ normalizer (X : Set G) → X ≤ d.MI I

/-- The component in the intrinsic Thompson subgroup is a subgroup of `I`. -/
theorem component_le {d : LocalData G} {I : Subgroup G}
    (c : ComponentWitness d I) : c.L ≤ I :=
  c.le_thompson.trans (sSup_le fun _ hA => hA.1)

/-- The nontrivial two-core passes to every intermediate subgroup containing
the common Sylow subgroup. -/
theorem intermediate_core_ne_bot [Finite G]
    {S I J : Subgroup G} (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = S)
    (hI : I.pCoreIn 2 ≠ ⊥) (hSJ : S ≤ J) (hJI : J ≤ I) :
    J.pCoreIn 2 ≠ ⊥ := by
  have hcoreS : I.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow I P
  have hcoreJ : I.pCoreIn 2 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) (hcoreS.trans hSJ)
      (hJI.trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
  exact fun he => hI (eq_bot_iff.mpr (hcoreJ.trans he.le))

/-- Every proper overgroup of `Y₊S` inside a minimal outside `I` lies in `M_I`.
This proves uniqueness, not just maximality among two-local overgroups. -/
theorem proper_overgroup_le_intersection [Finite G]
    (d : LocalData G) {I J : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hYJ : d.Yplus ⊔ d.S ≤ J) (hJI : J < I) : J ≤ d.MI I := by
  apply le_inf ?_ hJI.le
  by_contra hJM
  have hJ : J ∈ d.Hplus :=
    ⟨⟨intermediate_core_ne_bot P hP hI.1.1.1
      (le_sup_right.trans hYJ) hJI.le, hYJ⟩, hJM⟩
  exact hJI.ne (hI.eq_of_ge hJ hJI.le).symm

/-- The precise unique-maximum formulation of the last assertion of 15.3.27(4).
In particular it quantifies over all proper subgroups containing `Y₊S`. -/
theorem intersection_unique_maximal [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hYM : d.Yplus ≤ d.M) :
    d.Yplus ⊔ d.S ≤ d.MI I ∧ d.MI I < I ∧
      ∀ J : Subgroup G, d.Yplus ⊔ d.S ≤ J → J < I → J ≤ d.MI I := by
  refine ⟨le_inf (sup_le hYM (inf_le_left.trans d.sylow_le)) hI.1.1.2,
    lt_of_le_of_ne inf_le_right ?_, fun _ => proper_overgroup_le_intersection d hI P hP⟩
  intro he
  exact hI.1.2 (he ▸ inf_le_left)

/-- The minimal-outside conclusion of 15.3.27, conditional on its still
separate component-containment argument. -/
theorem lemma_15_3_27_4_of_containment [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (c : ComponentWitness d I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hYL : d.Yplus ≤ c.L) (hYM : d.Yplus ≤ d.M) :
    I = c.L ⊔ d.S ∧ d.Yplus ⊔ d.S ≤ d.MI I ∧ d.MI I < I ∧
      ∀ J : Subgroup G, d.Yplus ⊔ d.S ≤ J → J < I → J ≤ d.MI I :=
  ⟨RankOne.eq_component_join_sylow hI P hP (component_le c) hYL c.outside,
    intersection_unique_maximal d hI P hP hYM⟩

/-- The nontrivial plane action used in both exclusions 15.3.30 and 15.3.31.
It follows from the actual normalizer control, without any model tag. -/
theorem plane_action_ne_bot (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hnorm : normalizer (d.V₁ : Set G) ≤ d.M) : ⁅d.V₁, c.L⁆ ≠ ⊥ := by
  intro h
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
  exact c.outside (hc.trans ((Subgroup.centralizer_le_normalizer _).trans hnorm))

/-- The final contradiction common to the two small-component eliminations:
their extension calculations must prove the centralizer equality. -/
theorem excluded_of_equal_centralizers (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hVI : d.V₁ ≤ I)
    (hVY : d.V₁ ≤ centralizer (d.Yplus : Set G))
    (hnorm : normalizer (d.V₁ : Set G) ≤ d.M)
    (heq : I ⊓ centralizer (d.Yplus : Set G) = I ⊓ centralizer (c.L : Set G)) :
    False := by
  have hVL : d.V₁ ≤ centralizer (c.L : Set G) :=
    (le_inf hVI hVY).trans (heq.le.trans inf_le_right)
  exact plane_action_ne_bot d c hnorm (commutator_eq_bot_iff_le_centralizer.mpr hVL)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

end
