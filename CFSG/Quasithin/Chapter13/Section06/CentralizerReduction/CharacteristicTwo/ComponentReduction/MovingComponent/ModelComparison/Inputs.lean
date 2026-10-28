module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.LocalQuotients

/-!
# Intrinsic comparison contracts for the moving component

These are the remaining carrier comparisons needed to intersect the full
field-indexed characteristic-two list with 1.2.1(3). The classical and
exceptional families can be treated independently. Each field refers to
actual group equivalences, and none assumes the narrowed output list.
The triality comparison is proved separately from its existing root geometry.

`SourceInput` keeps the literal marked action, both Sylow witnesses, the
complete 1.1.5 action alternative, and the actual four-group containment.
Its local normal-or-two-conjugates premise is exactly the explicit earlier
1.2.1(3) input; it does not assert the comparison sought here.

Source: Aschbacher–Smith, 1.1.5(3), pp.501–503, 1.2.1(3), p.504,
and the moving-component paragraph of 13.6.6, p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
open Chapter1.Section02 Chapter1.Section02.LocalModels ClassificationModels
open InitialSieve A5Module
open Chapter15.Section03.Candidates.ComponentStructure

/-- The three larger classical binary families are absent from the nonnormal list. -/
structure ClassicalExclusions (Q : Type*) [Group Q] : Prop where
  unitary : ∀ m : ℕ, 2 ≤ m → ClassicalGroup.IsPSU Q 3 (2 ^ m) →
    ¬ NonnormalCComponentModel Q
  linear : ∀ m : ℕ, 2 ≤ m → ClassicalGroup.IsPSL Q 3 (2 ^ m) →
    ¬ NonnormalCComponentModel Q
  symplectic : ∀ m : ℕ, 2 ≤ m → ClassicalGroup.IsPSp Q 2 (2 ^ m) →
    ¬ NonnormalCComponentModel Q

/-- The two remaining exceptional binary families, with their concrete carriers. -/
structure ExceptionalExclusions (Q : Type*) [Group Q] : Prop where
  g2 : ∀ m : ℕ, 2 ≤ m → IsG2At Q (2 ^ m) → ¬ NonnormalCComponentModel Q
  ree : ∀ n : ℕ, 1 ≤ n → IsReeF4At Q n → ¬ NonnormalCComponentModel Q

/-- The rank-one conclusion preserves the supplied exponent, even for Suzuki. -/
def RankOneAt (Q : Type*) [Group Q] (m : ℕ) : Prop :=
  ClassicalGroup.IsPSL Q 2 (2 ^ m) ∨
    ∃ n : ℕ, 1 ≤ n ∧ m = 2 * n + 1 ∧
      Nonempty (Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n)

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- Genuine local input after the large-field branch of the initial sieve.
The actual two-cover alternatives remain in `modelAction`; the component
is not required to be centerless. -/
structure SourceInput (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (m : ℕ) : Prop where
  component : IsComponent (Gv (markedV s)) K
  oddCore : pPrimeCore 2 (Gv (markedV s)) = ⊥
  sylow : ∃ P : Sylow 2 (Gv (markedV s)),
    (P : Subgroup (Gv (markedV s))) = localT T (markedV s)
  action : ActionData s T K
  modelAction : ModelAction115 K (K.normalizerMonoidHom ⟨zLocal s, action.z_normalizes⟩)
  moving : ¬ localT T (markedV s) ≤ X K
  localModels : K.Normal ∨
    (Set.range fun g : Gv (markedV s) => K.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
      NonnormalCComponentModel (K ⧸ pCore 2 K)
  exponent : 1 < m
  binaryModel : BinaryModelAt (NormalizerAction.componentImage K) m
  four_in_component : EStar s K action.a_normalizes action.z_normalizes ≤
    NormalizerAction.componentImage K

universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

/-- The source setup and the published large-field witness instantiate all
inputs of the comparison, without changing the field exponent or the action. -/
theorem sourceInput_of_largeField (d : Setup κ T s)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    (h115 : ModelAction115 K (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩))
    (hmove : ¬ localT (T : Subgroup G) (markedV s) ≤ X K)
    (h121 : K.Normal ∨
      (Set.range fun g : Gv (markedV s) => K.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
        NonnormalCComponentModel (K ⧸ pCore 2 K))
    (hlarge : LargeField K a) : ∃ m, SourceInput s (T : Subgroup G) K m := by
  obtain ⟨m, hm, hb, hE⟩ := hlarge
  exact ⟨m, hK, hodd,
    ⟨d.sylow, (localT_eq_sylow _ _ d.sylow d.sylow_image).symm⟩,
    a, h115, hmove, h121, hm, hb, hE⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
