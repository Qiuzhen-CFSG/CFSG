module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Sporadic.Reduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Sporadic.RudvalisReduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.SmallModels
public import Theory.Mathieu.M12.Properties.SylowFixedActions
public import Theory.Mathieu.M22.Properties.ElementarySylowFixers
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers
public import Theory.Mathieu.M24.Properties.ElementarySylowFixers
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ElementarySylowFixers
public import Theory.SpecificGroups.Held.LocalPairs.SylowPointwise
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations

/-!
# Sporadic components in the initial sieve

The source four-group cannot act faithfully while fixing a Sylow subgroup
pointwise in M₁₁, M₁₂, M₂₂, M₂₃, M₂₄, J₂, J₄ or HS. Intrinsic fixer
calculations and actual cyclic Sylow centers give the required bound of two. The central quotient bridge includes
components with nontrivial two-core.

Held has the same consequence conditional on its full automorphism
realization. The all-ten-case assembly below explicitly retains that input
and the intrinsic Ru fixer bound. It does not assert the source
exclusion until these remaining model inputs have been discharged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(f), printed pp.501–503, and proof of 13.6.6, printed p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
open A5Module ClassificationModels
open Chapter15.Section03.Candidates.ComponentStructure
open _root_.Sporadic.Mathieu

theorem m12_smallSylowFixers : SmallSylowFixers M12 := by
  intro _ _ _ P A _ hfix
  exact m12_faithful_sylow_fixed_action_card_le_two P A.subtype A.subtype_injective
    (fun a x => hfix a a.property x x.property)

theorem m22_smallSylowFixers : SmallSylowFixers M22 := by
  intro _ _ _ P A _ hfix
  exact m22_elementary_sylow_fixer_card_le_two
    (center_eq_bot_of_simple_perfect M22) P A hfix

theorem m23_smallSylowFixers : SmallSylowFixers M23 := by
  intro _ _ _ P A _ hfix
  exact m23_elementary_sylow_fixer_card_le_two
    (center_eq_bot_of_simple_perfect M23) P A hfix

theorem m24_smallSylowFixers : SmallSylowFixers M24 := by
  intro _ _ _ P A _ hfix
  exact m24_elementary_sylow_fixer_card_le_two
    (center_eq_bot_of_simple_perfect M24) P A hfix

theorem j4_smallSylowFixers : SmallSylowFixers Janko4.Model := by
  intro _ _ _ P A _ hfix
  exact Janko4.elementary_sylow_fixer_card_le_two
    (center_eq_bot_of_simple_perfect Janko4.Model) P A hfix

theorem j2_smallSylowFixers : SmallSylowFixers _root_.Sporadic.LeechRelated.J2.Carrier := by
  intro _ _ _ P A _ hfix
  exact _root_.Sporadic.LeechRelated.J2.elementary_sylow_fixer_card_le_two
    (center_eq_bot_of_simple_perfect _) P A hfix

theorem hs_smallSylowFixers : SmallSylowFixers _root_.Sporadic.LeechRelated.HS.Carrier := by
  intro _ _ _ P A _ hfix
  exact _root_.Sporadic.LeechRelated.HS.ElementarySylowFixers.sylow_fixer_card_le_two P A hfix

/-- Only full intrinsic automorphism realization remains in this Held adapter.
Its producer may use the simplicity and perfectness inherited from the component. -/
theorem held_smallSylowFixers_of_realization
    (hrealize : ∀ [IsSimpleGroup Held.He] [Group.IsPerfect Held.He],
      Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    SmallSylowFixers Held.He := by
  intro _ _ _ P A _ hfix
  let : IsCyclic (center P) := isCyclic_of_card_dvd_prime (p := 2) (by
    rw [Held.LocalPairs.SylowGeometry.Calculations.inner_center_card])
  apply Theory.GroupAction.elementary_sylow_fixer_card_le_two_of_inner P
    (center_eq_bot_of_simple_perfect Held.He) _ A hfix
  intro α _ hα
  obtain ⟨g, hg⟩ := Held.LocalPairs.SylowPointwise.isInner_of_fixes_sylow hrealize P α
    (fun x hx => hα ⟨x, hx⟩)
  exact ⟨g, hg.symm⟩

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

theorem not_m12_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* M12) :=
  not_quotient_of_smallSylowFixers m12_smallSylowFixers K hK hodd a

theorem not_m22_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* M22) :=
  not_quotient_of_smallSylowFixers m22_smallSylowFixers K hK hodd a

theorem not_m23_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* M23) :=
  not_quotient_of_smallSylowFixers m23_smallSylowFixers K hK hodd a

theorem not_m24_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* M24) :=
  not_quotient_of_smallSylowFixers m24_smallSylowFixers K hK hodd a

theorem not_j4_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) :=
  not_quotient_of_smallSylowFixers j4_smallSylowFixers K hK hodd a

theorem not_j2_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* _root_.Sporadic.LeechRelated.J2.Carrier) :=
  not_quotient_of_smallSylowFixers j2_smallSylowFixers K hK hodd a

theorem not_hs_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* _root_.Sporadic.LeechRelated.HS.Carrier) :=
  not_quotient_of_smallSylowFixers hs_smallSylowFixers K hK hodd a

/-- All ten literal source carriers are retained. The remaining intrinsic
model facts are explicit premises, to be discharged by this task's final assembly. -/
theorem not_sporadic_quotient_of_remaining
    (hRu : SmallSylowFixers Rudvalis.Model)
    (hHe : ∀ [IsSimpleGroup Held.He] [Group.IsPerfect Held.He],
      Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    {κ : GroupClass} (_d : Setup κ T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K)
    (name : SporadicName) (hne : name ≠ .j3)
    (e : (K ⧸ pCore 2 K) ≃* name.Carrier)
    (_hz : TwoCentralInner (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩)) : False := by
  cases name with
  | m11 => exact ModelExclusions.not_m11_quotient K hK hodd a ⟨e⟩
  | m12 => exact not_m12_quotient K hK hodd a ⟨e⟩
  | m22 => exact not_m22_quotient K hK hodd a ⟨e⟩
  | m23 => exact not_m23_quotient K hK hodd a ⟨e⟩
  | m24 => exact not_m24_quotient K hK hodd a ⟨e⟩
  | j2 => exact not_quotient_of_smallSylowFixers j2_smallSylowFixers K hK hodd a ⟨e⟩
  | j3 => exact (hne rfl).elim
  | j4 => exact not_j4_quotient K hK hodd a ⟨e⟩
  | hs => exact not_quotient_of_smallSylowFixers hs_smallSylowFixers K hK hodd a ⟨e⟩
  | he =>
    exact not_quotient_of_smallSylowFixers
      (held_smallSylowFixers_of_realization hHe) K hK hodd a ⟨e⟩
  | ru => exact not_quotient_of_smallSylowFixers hRu K hK hodd a ⟨e⟩

/-- Source application with just the three independent intrinsic producer inputs:
Held realization, Rudvalis Sylow centers, and Rudvalis point-stabilizer preservation. -/
theorem not_sporadic_quotient_of_intrinsic_inputs
    (hRuCenter : ∀ [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
      (P : Sylow 2 Rudvalis.Model), Nat.card (center P) ≤ 2)
    (hRuStable : ∀ [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
      (f : MulAut Rudvalis.Model), ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y)
    (hHe : ∀ [IsSimpleGroup Held.He] [Group.IsPerfect Held.He],
      Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    {κ : GroupClass} (d : Setup κ T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K)
    (name : SporadicName) (hne : name ≠ .j3)
    (e : (K ⧸ pCore 2 K) ≃* name.Carrier)
    (hz : TwoCentralInner (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩)) : False :=
  not_sporadic_quotient_of_remaining
    (rudvalis_smallSylowFixers_of_centers_and_stabilizers hRuCenter hRuStable)
    hHe d K hK hodd a name hne e hz

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
