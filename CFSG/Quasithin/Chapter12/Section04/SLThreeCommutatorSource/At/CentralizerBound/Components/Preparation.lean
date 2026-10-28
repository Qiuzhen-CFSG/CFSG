module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Cases
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Layer

/-!
# The ordinary seed interface for the L₃ centralizer branch

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

This file records the part of the ordinary-component branch which is already
available from the common preparation and the proved ordinary-layer theorem.
The model reduction and the conjugator comparison remain separate source
obligations.  Keeping this wrapper here prevents later proofs from silently
changing the literal centralizer or subtype map.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815.
-/

public section

open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
universe u

/-- The literal ordinary-layer conclusion available once the source model
has identified the component as a Fermat/Mersenne PSL₂.  The subgroup `U₀`
is kept explicit because the later A.3.12 comparison is relative to this
particular plane centralizer. -/
theorem Configuration.seed_layer_of_fermatMersenne
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V U : Subgroup G}
    (c : Configuration T L V U)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer (U : Set G)))
    (U₀ : Subgroup G) (hU₀U : U₀ ≤ U) (hU₀ : U₀ ≠ ⊥)
    {q : ℕ} (hq : IsFermatOrMersennePrime q)
    (hmodel : ClassicalGroup.IsPSL K 2 q) :
    IsSQTK KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) ∧
      K ≤ (componentLayer (centralizer (U₀ : Set G))).map
        (centralizer (U₀ : Set G)).subtype := by
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le c.le_module
  have hU : IsPGroup 2 U := IsElementaryAbelian.isPGroup 2 U
  exact CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.seed_layer_of_fermatMersenne
    c.hypothesis.simpleQTKE
    U U₀ K hU hU₀U hU₀ hK hq hmodel

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound

