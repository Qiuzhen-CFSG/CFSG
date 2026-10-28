module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.Triality
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.ClassicalExclusions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.ExceptionalExclusions

/-!
# Comparing the moving-component model lists

The moving hypothesis forces the index-two orbit from genuine 1.2.1(3).
After identifying K/O₂(K), K/Z(K), and the literal K* in N(K)/C(K), we
intersect its model list with the complete `BinaryModelAt` list. The two
rank-one constructors retain the original field exponent; every exponent-one
endpoint is excluded by m > 1. The classical and exceptional exclusions use
proved intrinsic order comparisons and root geometry. `source_comparison`
discharges all carrier-exclusion premises on the actual component image;
`largeField_comparison` applies it to the published initial-sieve interface.
The genuine earlier normal-or-two-conjugates conclusion remains an explicit
input, as does the complete large-field branch of 1.1.5.

The PSL₂ branch supplies divisibility by three on the actual image of K
in H/O₂(H), as required by 1.2.2(a). No residual equality is assumed or
asserted, and the component's center is retained throughout, including m = 3.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3a,b), pp.501–503, 1.2.1(3) and 1.2.2(a), p.504,
and the moving-component paragraph of 13.6.6, p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
open Chapter1.Section02 InitialSieve A5Module
open Chapter15.Section03.Candidates.ComponentStructure

/-- Exhaust the field-indexed list. Only the stated intrinsic classical and
exceptional exclusions remain to be supplied; triality and all small-field
endpoints are discharged here. No field parameter is renamed. -/
theorem rankOneAt_of_exclusions {Q : Type*} [Group Q] {m : ℕ}
    (hclassical : ClassicalExclusions Q) (hexceptional : ExceptionalExclusions Q)
    (hm : 1 < m) (hbinary : BinaryModelAt Q m) (hnormal : NonnormalCComponentModel Q) :
    RankOneAt Q m := by
  cases hbinary with
  | linear_two _ _ iso => exact Or.inl iso
  | unitary_three m hm iso => exact (hclassical.unitary m hm iso hnormal).elim
  | suzuki n hn iso => exact Or.inr ⟨n, hn, rfl, iso⟩
  | linear_three m _ iso => exact (hclassical.linear m (by omega) iso hnormal).elim
  | symplectic m hm iso => exact (hclassical.symplectic m hm iso hnormal).elim
  | g2 m hm iso => exact (hexceptional.g2 m hm iso hnormal).elim
  | triality _ hf iso => exact (triality_not_nonnormal hf iso hnormal).elim
  | ree n hn iso => exact (hexceptional.ree n hn iso hnormal).elim
  | symplectic_derived _ => omega
  | g2_derived _ => omega
  | tits _ => omega
  | binary_linear _ _ _ => omega

/-- Intersect the complete characteristic-two and nonnormal lists using the
proved intrinsic comparisons, preserving the original field exponent. -/
theorem rankOneAt_of_models {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] {m : ℕ}
    (hm : 1 < m) (hbinary : BinaryModelAt Q m)
    (hnormal : NonnormalCComponentModel Q) : RankOneAt Q m :=
  rankOneAt_of_exclusions (classical_exclusions Q) (exceptional_exclusions Q)
    hm hbinary hnormal

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Subgroup G} {K : Subgroup (Gv (markedV s))} {m : ℕ}

/-- The local comparison output, including the precise input needed by 1.2.2(a). -/
structure Conclusion (K : Subgroup (Gv (markedV s))) (m : ℕ) : Prop where
  index : (X K).index = 2
  model : RankOneAt (NormalizerAction.componentImage K) m
  psl_three : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 (2 ^ m) →
    3 ∣ Nat.card (NormalizerAction.componentImage K) ∧
      3 ∣ Nat.card (K ⧸ pCore 2 K) ∧
      3 ∣ Nat.card (K.map (QuotientGroup.mk' (pCore 2 (Gv (markedV s)))))

/-- Apply the intrinsic comparison to the actual marked local group and its
quotient maps. The two carrier-exclusion premises remain assembly obligations. -/
theorem source_comparison_of_exclusions
    (hclassical : ClassicalExclusions (NormalizerAction.componentImage K))
    (hexceptional : ExceptionalExclusions (NormalizerAction.componentImage K))
    (d : SourceInput s T K m) : Conclusion K m := by
  obtain ⟨hi, hmodel⟩ := moving_index_and_image_model d.oddCore
    (localT T (markedV s)) K d.component d.moving d.localModels
  exact ⟨hi, rankOneAt_of_exclusions hclassical hexceptional d.exponent
    d.binaryModel hmodel, psl2_three_divides_quotients d.oddCore d.component⟩

universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

/-- Instantiate uniform intrinsic model comparisons on the literal component
image. Its finite simple perfect hypotheses follow from the actual component;
no separate simplicity certification of a concrete model is needed. -/
theorem source_comparison_of_uniform_exclusions
    (hclassical : ∀ (Q : Type u) [Group Q] [Finite Q] [IsSimpleGroup Q]
      [Group.IsPerfect Q], ClassicalExclusions Q)
    (hexceptional : ∀ (Q : Type u) [Group Q] [Finite Q] [IsSimpleGroup Q]
      [Group.IsPerfect Q], ExceptionalExclusions Q)
    {U : Subgroup G} {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (d : SourceInput s U K m) : Conclusion K m := by
  let := componentImage_simple d.component
  let := componentImage_perfect d.component
  exact source_comparison_of_exclusions (hclassical _) (hexceptional _) d

/-- The moving-component comparison in 13.6.6, conditional only on the
genuine earlier local inputs. The component supplies simplicity and
perfectness of its image, and both intrinsic exclusion families are proved.
No centerless-component or residual-equality premise is introduced. -/
theorem source_comparison
    {U : Subgroup G} {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (d : SourceInput s U K m) : Conclusion K m :=
  source_comparison_of_uniform_exclusions classical_exclusions exceptional_exclusions d

/-- Consumer of the published large-field sieve interface, preserving its
literal four-group, actual Sylow witnesses and full 1.1.5 model action.
The supplied carrier exclusions are the only additional comparison inputs. -/
theorem largeField_comparison_of_exclusions (d : Setup κ T s)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    (h115 : ModelAction115 K (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩))
    (hmove : ¬ localT (T : Subgroup G) (markedV s) ≤ X K)
    (h121 : K.Normal ∨
      (Set.range fun g : Gv (markedV s) => K.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
        NonnormalCComponentModel (K ⧸ pCore 2 K))
    (hlarge : LargeField K a)
    (hclassical : ClassicalExclusions (NormalizerAction.componentImage K))
    (hexceptional : ExceptionalExclusions (NormalizerAction.componentImage K)) :
    ∃ m, SourceInput s (T : Subgroup G) K m ∧ Conclusion K m := by
  obtain ⟨m, hm⟩ := sourceInput_of_largeField d hodd K hK a h115 hmove h121 hlarge
  exact ⟨m, hm, source_comparison_of_exclusions hclassical hexceptional hm⟩

/-- Apply the completed model comparison to the actual marked action and
large-field sieve output. The returned source witness retains both Sylow
witnesses, the literal central four-group, and all central-cover alternatives.
In the PSL₂ branch the conclusion includes three-divisibility on the exact
ambient two-core quotient image used by 1.2.2(a). -/
theorem largeField_comparison (d : Setup κ T s)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    (h115 : ModelAction115 K (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩))
    (hmove : ¬ localT (T : Subgroup G) (markedV s) ≤ X K)
    (h121 : K.Normal ∨
      (Set.range fun g : Gv (markedV s) => K.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
        NonnormalCComponentModel (K ⧸ pCore 2 K))
    (hlarge : LargeField K a) :
    ∃ m, SourceInput s (T : Subgroup G) K m ∧ Conclusion K m := by
  obtain ⟨m, hm⟩ := sourceInput_of_largeField d hodd K hK a h115 hmove h121 hlarge
  exact ⟨m, hm, source_comparison hm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
