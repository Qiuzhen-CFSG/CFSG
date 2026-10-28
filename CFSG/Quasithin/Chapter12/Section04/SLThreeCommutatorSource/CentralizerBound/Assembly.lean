module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Cases
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Preparation
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Application
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Layer
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.Preparation
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.Models
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.Exclusion
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore.Closure.Source
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore.Layer.Source
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Assembly
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter

/-!
# Assembly interfaces for the three cases of 12.4.8

An escaping hyperplane either has a component, has a characteristic-two
centralizer, or has a nontrivial odd core. In the last deduction, absence
of components makes the prime-core product self-centralizing. This proves
that the three separately stated case exclusions suffice, and connects
them to the original noncommuting-conjugate consumer.

The general conditional interfaces are preserved. All three local cases are
proved and discharged in `hyperplaneCentralizers` and its literal consumers.
Only the genuine earlier 12.2 and 12.4.1 source inputs remain explicit, with
final discharge owned by qt-d-1242-l3-commutator-source.

Source: Aschbacher–Smith, 12.4.8–9, printed pp.815–816.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Section02 SmallFusion
universe u

/-- Assemble all source cases, retaining their precise undischarged obligations. -/
theorem hyperplaneCentralizers_of_cases
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (characteristicTwo : CharacteristicTwoExclusion.{u})
    (components : ComponentExclusion.{u})
    (oddCore : OddCoreExclusion.{u}) : HyperplaneCentralizers1248.{u} := by
  intro G _ _ T L V h D hmodel hne U hUV hcor
  by_contra hescape
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  let c : Configuration T L V U :=
    ⟨h, D, E, hne, structural, normalizerAction G T L V h D hmodel hne,
      hUV, hcor, hescape⟩
  by_cases hc : HasCharacteristicTwo (centralizer (U : Set G))
  · exact characteristicTwo G T L V U c hc
  by_cases hcomp : ∃ K : Subgroup G, IsComponentIn K (centralizer (U : Set G))
  · exact components G T L V U c hcomp
  have hnc : ∀ K : Subgroup G, ¬ IsComponentIn K (centralizer (U : Set G)) :=
    fun K hK => hcomp ⟨K, hK⟩
  apply oddCore G T L V U c hnc
  intro ho
  apply hc
  let H := centralizer (U : Set G)
  have hnc' : ∀ J : Subgroup H, ¬ IsComponent H J := by
    intro J hJ
    apply hnc (J.map H.subtype)
    refine ⟨map_subtype_le J, ?_⟩
    have he : (J.map H.subtype).subgroupOf H = J :=
      comap_map_eq_self_of_injective H.subtype_injective J
    rwa [he]
  have hh := centralizer_core_product_le_of_no_components 2 hnc'
  change pPrimeCore 2 H = ⊥ at ho
  simpa only [HasCharacteristicTwo, ho, sup_bot_eq] using hh

/-- Actual application to the original commutator-plane consumer. This
retains the three case obligations and the independently owned 12.4.1 input. -/
theorem source_commutator_plane_of_cases
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (characteristicTwo : CharacteristicTwoExclusion.{u})
    (components : ComponentExclusion.{u})
    (oddCore : OddCoreExclusion.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane structural marked normalizerAction
    (hyperplaneCentralizers_of_cases structural marked normalizerAction
      characteristicTwo components oddCore) conjugate T L V h D hmodel hne

/-- The remaining two cases suffice after the proved ordinary-component exclusion. -/
theorem hyperplaneCentralizers_of_noncomponent_cases
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (characteristicTwo : CharacteristicTwoExclusion.{u})
    (oddCore : OddCoreExclusion.{u}) : HyperplaneCentralizers1248.{u} :=
  hyperplaneCentralizers_of_cases structural marked normalizerAction
    characteristicTwo ordinaryComponentExclusion oddCore

/-- Actual application to the original commutator-plane consumer. The
ordinary-component case is proved; the two other cases and the independently
owned 12.4.1 input remain explicit. -/
theorem source_commutator_plane_of_noncomponent_cases
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (characteristicTwo : CharacteristicTwoExclusion.{u})
    (oddCore : OddCoreExclusion.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane structural marked normalizerAction
    (hyperplaneCentralizers_of_cases structural marked normalizerAction
      characteristicTwo ordinaryComponentExclusion oddCore) conjugate T L V h D hmodel hne

/-- Literal classification consumer of the constructed L₃ geometry.
Only the pointwise block-selection and index arguments, the independent
odd-core case and earlier 12.4.1 input remain with their source owners. -/
theorem source_commutator_plane_of_block_inputs
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (selection : ∀ (G : Type u) [Group G] [Finite G]
      (T : Sylow 2 G) (L V U : Subgroup G) (c : Configuration T L V U),
        CharacteristicTwo.BlockSelection c)
    (index : ∀ (G : Type u) [Group G] [Finite G]
      (T : Sylow 2 G) (L V U : Subgroup G) (c : Configuration T L V U),
        CharacteristicTwo.BlockIndex c)
    (oddCore : OddCoreExclusion.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane structural marked normalizerAction
    (hyperplaneCentralizers_of_cases structural marked normalizerAction
      (CharacteristicTwo.characteristicTwoExclusion_of_block_inputs selection index)
      ordinaryComponentExclusion oddCore) conjugate T L V h D hmodel hne

/-- Only the odd-core case remains after the two proved case exclusions.
Its discharge belongs to the final 12.4.8 assembly. -/
theorem hyperplaneCentralizers_of_oddCore
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (oddCore : OddCoreExclusion.{u}) : HyperplaneCentralizers1248.{u} :=
  hyperplaneCentralizers_of_cases structural marked normalizerAction
    CharacteristicTwo.characteristicTwoExclusion ordinaryComponentExclusion oddCore

/-- Feed the proved characteristic-two and component exclusions to the literal
commutator-plane consumer. The independent odd-core case and earlier-source
inputs remain with the final 12.4.8 and 12.4.2 assembly owners. -/
theorem source_commutator_plane_of_oddCore
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (oddCore : OddCoreExclusion.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane structural marked normalizerAction
    (hyperplaneCentralizers_of_oddCore structural marked normalizerAction oddCore)
    conjugate T L V h D hmodel hne

/-- The odd closure construction is proved. Ordinary-layer centralization is
the remaining local obligation of this 12.4.8 assembly. -/
theorem hyperplaneCentralizers_of_layer
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (layer : OddCore.LayerCentralization.{u}) : HyperplaneCentralizers1248.{u} :=
  hyperplaneCentralizers_of_oddCore structural marked normalizerAction
    (OddCore.oddCoreExclusion_of_layer layer)

/-- Feed the constructed odd closure and both completed cases to the literal
commutator-plane consumer. Layer centralization stays with the 12.4.8 owner;
the earlier-source premises stay with qt-d-1242-l3-commutator-source. -/
theorem source_commutator_plane_of_layer
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (layer : OddCore.LayerCentralization.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane_of_oddCore structural marked normalizerAction
    (OddCore.oddCoreExclusion_of_layer layer) conjugate T L V h D hmodel hne

/-- The original L₃ instance of 12.4.8. All three local cases are proved;
the genuine earlier 12.2 inputs remain with qt-d-1242-l3-commutator-source. -/
theorem hyperplaneCentralizers
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u}) : HyperplaneCentralizers1248.{u} :=
  hyperplaneCentralizers_of_oddCore structural marked normalizerAction
    OddCore.oddCoreExclusion

/-- Apply the complete 12.4.8 bound to the original symmetric commutator plane.
Only the previously declared earlier-source inputs remain explicit. -/
theorem source_commutator_plane_of_proved_centralizers
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane_of_oddCore structural marked normalizerAction
    OddCore.oddCoreExclusion conjugate T L V h D hmodel hne

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
