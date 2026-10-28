module

public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.NormalLift
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels

/-!
# The ordinary balance inputs in E.6.18 and E.6.22--25

An ordinary centralizer component restricts to the literal centralizer
subtype, where the rank-two source I.3.1(3) applies. With trivial ambient
odd core, its orbit equality is already the ordinary-layer equality needed
by the Sylow-central inspection. The E.6.25 ordinary component is identified
with the existing C-component by the earlier unique-containment theorem.

The universal A.3.6, A.3.8 and GLS 5.22 orbit/projection implications remain
explicit inputs, owned by `qt-a03-sqtk-structure` and `qt-i-03-l-balance`.
These applications need no B₂ assertion. Source: Aschbacher--Smith,
E.6.18 and E.6.22--25, printed pp.252--256; I.3.1, pp.414--415.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceBalance
open ChapterI.RankTwoSource ComponentBalance Enlargement
universe u

/-- The exact universal I.3.1(3) input consumed by the two lifting arguments.
The local component is restricted to C_H(P), then mapped back by its subtype. -/
theorem normal_component_of_rank_two
    {K : GroupClass.{u}} (hA36 : EarlierA36 K) (hA38 : EarlierA38 K)
    (hGLS : EarlierOrbitProjection K)
    (H : Type u) [Group H] [Finite H] (hH : IsSQTK K H)
    (P D : Subgroup H) (hP : IsPGroup 2 P)
    (hD : CentralizerComponent P D) (hr : primeRank 3 D = 2) :
    ∃ J : Subgroup H, D ≤ J ∧ J.Normal ∧ IsComponent H J := by
  let C := centralizer (P : Set H)
  let L := D.subgroupOf C
  have hL : L.IsTwoComponent := ChapterI.Balance.ordinary_isTwoComponent hD.2
  have hrL : primeRank 3 L = 2 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hD.1)]
    exact hr
  obtain ⟨_, J, hJ, hn, hLJ⟩ :=
    lemma_I_3_1_three hA36 hA38 hGLS hH P hP L hL hrL
  have hDJ : D ≤ J := by
    simpa only [L, C, map_subgroupOf_eq_of_le hD.1] using hLJ
  exact ⟨J, hDJ, hn, hJ⟩

/-- Ordinary seeds and O(H)=1 give the full orbit equality in the existing
component-inspection contract; no projection quasisimplicity is assumed. -/
theorem earlierBalance_of_orbit_projection {K : GroupClass.{u}}
    (hGLS : EarlierOrbitProjection K) : ComponentInspection.EarlierBalance K := by
  intro H _ _ hH ho P D hP hD
  obtain ⟨J, hJ, horbit, _⟩ := hGLS H hH P hP
    (D.subgroupOf (centralizer (P : Set H)))
    (ChapterI.Balance.ordinary_isTwoComponent hD.2)
  rw [map_subgroupOf_eq_of_le hD.1] at horbit
  refine ⟨J, (ChapterI.Balance.ordinary_pumpup_of_orbit_eq ho P D J hJ horbit).1, ?_⟩
  simpa only [oddELayer, ho, ChapterI.Balance.twoComponentLayer_eq_componentLayer ho,
    bot_sup_eq, sup_bot_eq] using horbit

variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

/-- Supply I.3.1(3) in E.6.18, retaining precisely the original Theorem A,
Theorem C and seven-component action inspection inputs. -/
theorem seven_lifting_of_earlier_sources
    (hA36 : EarlierA36.{u} KnownSimple.IsKnownSimple)
    (hA38 : EarlierA38.{u} KnownSimple.IsKnownSimple)
    (hGLS : EarlierOrbitProjection.{u} KnownSimple.IsKnownSimple)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], IsSimpleGroup X →
      ¬ IsMulCommutative X → IsSQTK KnownSimple.IsKnownSimple X →
        Chapter1.Section02.LocalModels.TheoremCModel X)
    (hinspect : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      IsStronglyQuasithin X → Chapter1.Section02.LocalModels.TheoremCModel (X ⧸ center X) →
        SevenActionInspection X)
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) : SevenLifting V := by
  exact seven_lifting_of_inspection hA hC
    (normal_component_of_rank_two hA36 hA38 hGLS) hinspect h

/-- The E.6.18 exclusion with its I.3.1 input discharged and the original
model inspection and earlier E.6.8/E.6.13 statements retained. -/
theorem seven_excluded_of_earlier_sources [IsElementaryAbelian 2 V]
    (hA36 : EarlierA36.{u} KnownSimple.IsKnownSimple)
    (hA38 : EarlierA38.{u} KnownSimple.IsKnownSimple)
    (hGLS : EarlierOrbitProjection.{u} KnownSimple.IsKnownSimple)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], IsSimpleGroup X →
      ¬ IsMulCommutative X → IsSQTK KnownSimple.IsKnownSimple X →
        Chapter1.Section02.LocalModels.TheoremCModel X)
    (hinspect : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      IsStronglyQuasithin X → Chapter1.Section02.LocalModels.TheoremCModel (X ⧸ center X) →
        SevenActionInspection X)
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h8 : SevenEscape M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G)) :
    SevenExcluded M V := by
  intro A hΓ hc L hL
  exact exclude_seven_of_lifting h h15 h8 h13
    (seven_lifting_of_earlier_sources hA36 hA38 hGLS hA hC hinspect h)
    (seven_uniqueness h) hΓ hc hL

/-- Supply the rank-two normal component used by the A₆ enlargement in E.6.23. -/
theorem further_lift_of_earlier_sources
    (hA36 : EarlierA36.{u} KnownSimple.IsKnownSimple)
    (hA38 : EarlierA38.{u} KnownSimple.IsKnownSimple)
    (hGLS : EarlierOrbitProjection.{u} KnownSimple.IsKnownSimple)
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) :
    SixAutomorphisms.FurtherLift M V := by
  exact SixAutomorphisms.NormalLift.further_lift
    (normal_component_of_rank_two hA36 hA38 hGLS) h

/-- The actual A₆ orbit-containment consumer, retaining both existing model
identification and linear-action inputs and discharging its normal lift. -/
theorem six_orbit_containment_of_earlier_sources [IsElementaryAbelian 2 V]
    (hA36 : EarlierA36.{u} KnownSimple.IsKnownSimple)
    (hA38 : EarlierA38.{u} KnownSimple.IsKnownSimple)
    (hGLS : EarlierOrbitProjection.{u} KnownSimple.IsKnownSimple)
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h13 : ∀ B ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (B : Set G))
    (hmodel : SixAutomorphisms.ModelIdentification M V)
    (haction : SixAutomorphisms.LinearActionAnalysis M V) : SixOrbitContainment M V := by
  exact SixAutomorphisms.sixOrbitContainment_of_enlargement_analysis h h15 h13
    (further_lift_of_earlier_sources hA36 hA38 hGLS h) hmodel haction

variable {K : GroupClass.{u}}

/-- The E.6.22 component-inspection conclusion from the actual orbit producer.
The established model inspections are used internally by component_lift. -/
theorem component_lift_of_orbit_projection [IsElementaryAbelian 2 V]
    (hGLS : EarlierOrbitProjection K)
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      ¬ X ≤ M ∧ Components.ComponentAlternatives M V A
        (sylowCentralizer (T : Subgroup G) V) X) : ComponentLiftAlternative M V := by
  exact ComponentInspection.component_lift h h15
    (earlierBalance_of_orbit_projection hGLS) ho h68

/-- The actual characteristic-two conclusion in E.6.22, with only its
I.3 balance input replaced by the genuine universal orbit producer. -/
theorem characteristicTwo_of_orbit_projection [IsElementaryAbelian 2 V]
    (hGLS : EarlierOrbitProjection K)
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V) (earlier : EarlierLocalFacts T)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (h18 : SevenExcluded M V) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      ¬ X ≤ M ∧ Components.ComponentAlternatives M V A
        (sylowCentralizer (T : Subgroup G) V) X)
    (hbound : TwoConjugates M V) :
    ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) := by
  exact characteristicTwo_of_component_enlargement h h15 earlier h13 h18 ho
    (component_lift_of_orbit_projection hGLS h h15 ho h68) hbound

/-- In the actual exceptional E.6.25 configuration, an ordinary seed makes
the selected C-component ordinary. Uniqueness in 1.2.4 identifies it with
the orbit-produced ordinary component; the original subgroup J is retained. -/
theorem exceptional_enlargement_component_of_ordinary_seed
    (hGLS : EarlierOrbitProjection K) (h : HypothesisE61 K T M V)
    (containment : FrobeniusReduction.LocalFactors.EarlierLocalContainment K)
    (ho : OddCoreFree V) {U L W J : Subgroup G}
    (hU : U ∈ obstructionFamily M V) (hL : CentralizerComponent U L)
    (d : FrobeniusReduction.LocalFactors.ExceptionalModels.TwoCentralEnlargement M V U L W J) :
    CentralizerComponent W J := by
  obtain ⟨X, hLX, hX⟩ := ComponentInspection.exists_containing_component h
    (earlierBalance_of_orbit_projection hGLS) ho d.obstruction hU.1 d.subspace_le hL
  have hLC : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)) :=
    ⟨hL.1, (ChapterI.Balance.ordinary_isTwoComponent hL.2).1⟩
  obtain ⟨C, _, huniq⟩ := FrobeniusReduction.LocalFactors.exists_containing_cComponent h
    containment hU d.obstruction d.subspace_le hLC
  have hXC : X = C := huniq X
    ⟨⟨hX.1, (ChapterI.Balance.ordinary_isTwoComponent hX.2).1⟩, hLX⟩
  have hJC : J = C := huniq J ⟨d.component, d.proper.le⟩
  exact (hXC.trans hJC.symm) ▸ hX

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceBalance
