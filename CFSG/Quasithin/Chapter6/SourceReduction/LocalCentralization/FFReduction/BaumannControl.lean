module

public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceComplete
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourcePushingUp
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceExclusions
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceNonblock
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceBound
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction

/-!
# Rank-one Baumann control at the literal local Cartan consumer

The original rank-one Baumann bound is now proved for Input and its original
reduced W. Baumann escape forces the A5 branch, whose containing component
is neither ordinary nor a block. The original alternating-five layer theorem
excludes the remaining constrained nonblock configuration.

The final adapters package RankOneBaumannNormalizerControl and apply the
bound to the literal component_escape. Thus the constructed maximal local K
does not normalize Baum(T), retaining its omega-module and exceptional quotient.
The preceding conditional reductions remain available at their original APIs.

The exceptional quotient input is proved independently in ExceptionalModelsSource.
Final FF classification and assembly remain with
qt-d-1222-local-cartan-ff-source-classification.

Source: Aschbacher--Smith 5.1.7(1), pp.633--634, applied in 5.1.13, p.637.
-/

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

theorem Input.sylow_centralizer_eq_core
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    (T : Subgroup G) ⊓ centralizer (W : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := h.quotient_quasisimple
  exact Chapter5.RankOneBaumannSource.reduced_sylow_centralizer
    h.sylow_normalizes h.reduced.1 h.reduced_internal h.quotient_center_eq_bot h.noncentral

theorem Input.baumann_normalizer_of_thompson_centralizes
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let := h.quotient_quasisimple
  exact Chapter5.RankOneBaumannSource.baumann_normalizer_of_thompson_centralizes
    h.qtke h.maximal_local h.sylow_normalizes h.reduced.1 h.reduced_internal
    h.quotient_center_eq_bot h.noncentral hJ

theorem Input.sylow_centralizer_commutator_eq
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    (T : Subgroup G) ⊓ centralizer ((⁅W,L⁆ : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ centralizer (W : Set G) :=
  h.commutator_input.sylow_centralizer_eq_core.trans h.sylow_centralizer_eq_core.symm

theorem Input.thompson_moves_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
  fun hJ => hout (h.baumann_normalizer_of_thompson_centralizes hJ)

theorem Input.characteristic_baumann_eq_bot_of_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (D : Subgroup (ChapterB.baumann (T : Subgroup G))) (hD : D.Characteristic)
    (hn : ((D.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal) : D = ⊥ :=
  Chapter5.RankOneBaumannSource.characteristic_baumann_eq_bot_of_escape
    h.qtke h.maximal_local h.sylow_normalizes hout D hD hn

theorem localCartan_maximal_models_of_thompson_centralizes
    (hmodels : ExceptionalLocalOvercomponentModels G)
    {H A Y X D : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  obtain ⟨K,hXK,hK,hn,_,hU,hUne,hspan⟩ :=
    localCartan_maximal_reduced_configuration h hH hY d hXC
  refine ⟨K,hXK,hK,hn,?_,?_,hU,hUne,hspan⟩
  · exact hmodels h.qtke T X K (d.mem_localFamily hH.1.1.2 hY)
      (d.sylow_normalizes hH.1.1.2 hY.2) hK hXK d.component_model
  · intro hKB
    exact d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2
      (hXK.trans (hKB.trans (h.baumann_normalizer_of_thompson_centralizes hJ)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- At the literal Cartan consumer, normalization of Baum(T) excludes the
earlier case-three MS construction. The remaining source producer must
construct this data in the constrained nonblock branch at the original scope. -/
theorem LocalCartanWitness.original_nonblock_ms_false_of_baumann_normalizes
    {H A Y X D K : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hXK : X ≤ K)
    (hKB : K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (c : SourceConfiguration T L) {m : ℕ} (ms : Nonblock.MSData c m) : False :=
  h.original_nonblock_ms_false (fun hb =>
    d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2 (hXK.trans (hKB.trans hb))) c ms

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory Chapter4
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- If the constructed Cartan overcomponent normalizes Baum(T), its literal
component escape supplies the original A₅ pushing-up counterexample. The
remaining source exclusion must rule this out to complete the Baumann input. -/
theorem LocalCartanWitness.original_a5_counterexample_of_baumann_normalizes
    {H A Y X D K : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hXK : X ≤ K)
    (hKB : K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    ChapterC.IsAlternatingBlock L 5 ∧ (ChapterC.blockU L).map L.subtype = ⁅W,L⁆ ∧
    ∃ J N : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L L) ∧
      L ≤ J ∧ IsMaximalTwoLocal N ∧ J ≤ N ∧
      ¬ N ≤ normalizer (L : Set G) ∧ N ⊓ normalizer (L : Set G) < N ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple N (N ⊓ normalizer (L : Set G))
        L (J.pCoreIn 2) ⁅W,L⁆ :=
  h.original_a5_counterexample_of_baumann_escape (fun hb =>
    d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2 (hXK.trans (hKB.trans hb)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The literal classification consumer after discharging the centralizing and
natural branches: either the original A5 block remains, or the constructed
maximal local component escapes the Baumann normalizer. The A5 contradiction
is still needed to establish RankOneBaumannNormalizerControl. -/
theorem localCartan_maximal_models_or_original_alternating_block
    (hmodels : ExceptionalLocalOvercomponentModels G)
    {H A Y X D : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    (ChapterC.IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      ChapterC.IsAlternatingBlock L 5 ∧ (ChapterC.blockU L).map L.subtype = ⁅W,L⁆ ∧
      L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) ∨
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  classical
  by_cases hb : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)
  · right
    obtain ⟨K,hXK,hK,hn,_,hU,hUne,hspan⟩ :=
      localCartan_maximal_reduced_configuration h hH hY d hXC
    refine ⟨K,hXK,hK,hn,?_,?_,hU,hUne,hspan⟩
    · exact hmodels h.qtke T X K (d.mem_localFamily hH.1.1.2 hY)
        (d.sylow_normalizes hH.1.1.2 hY.2) hK hXK d.component_model
    · intro hKB
      exact d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2
        (hXK.trans (hKB.trans hb))
  · exact Or.inl (h.alternating_block_of_baumann_escape hb)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- If the literal constructed K normalizes Baum(T), component_escape forces
an actual conjugate of the original [W,L] outside O2(L Baum(T)). This is the
remaining A5 crossing configuration in the classification consumer. -/
theorem LocalCartanWitness.conjugate_core_of_baumann_normalizes
    {H A Y X D K : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hXK : X ≤ K)
    (hKB : K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    ∃ g ∈ normalizer (ChapterB.baumann (T : Subgroup G) : Set G),
      g ∉ normalizer (L : Set G) ∧
      ¬(⁅W,L⁆ : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom ≤
        (L ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 :=
  h.exists_baumann_conjugate_core_escape (fun hb =>
    d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2 (hXK.trans (hKB.trans hb)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly at the exact shared boundary. Only the original A5
branch's earlier uniqueness over L remains; no chosen module or model exclusions
are added to Input. This premise must be discharged before source 5.1.7 is complete. -/
theorem rankOneBaumannNormalizerControl_of_alternating_uniqueness
    (hu : ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
      Input KnownSimple.IsKnownSimple T L W n → ChapterC.IsAlternatingBlock L 5 →
      ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G)) :
    RankOneBaumannNormalizerControl G := by
  intro T L W n h
  exact h.baumann_normalizer_of_alternating_uniqueness (hu T L W n h)

/-- The literal FF consumer after the A5 crossing and dihedral calculations.
The only remaining source inputs are earlier uniqueness in the original A5
branch and the independently owned exceptional overcomponent quotients. -/
theorem localCartan_maximal_models_of_alternating_uniqueness
    (hmodels : ExceptionalLocalOvercomponentModels G)
    (hu : ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
      Input KnownSimple.IsKnownSimple T L W n → ChapterC.IsAlternatingBlock L 5 →
      ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G))
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) :=
  localCartan_maximal_models_of_earlier_inputs hmodels
    (rankOneBaumannNormalizerControl_of_alternating_uniqueness hu) h hH hY d hXC

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory ChapterC Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The original disjunctive Cartan adapter. The sharper adapter below also
discharges its ordinary component branch. -/
theorem LocalCartanWitness.original_a5_source_branches_of_baumann_normalizes
    {H A Y X D K : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hXK : X ≤ K)
    (hKB : K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    IsAlternatingBlock L 5 ∧
    Chapter4.Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⁅W,L⁆ ∧
    (∀ c : SourceConfiguration T L, ¬ Nonempty (OrdinarySymplecticMarking c n)) ∧
    ((∃ (c : OutsideChoice T L) (J : Subgroup c.H),
        IsComponent c.H J ∧ J.Normal ∧ IsQuasisimple (J ⧸ pCore 2 J) ∧
        L ≤ J.map c.H.subtype ∧ ¬ J.map c.H.subtype ≤ normalizer (L : Set G) ∧
        HypothesisC28 KnownSimple.IsKnownSimple c.H (c.H ⊓ normalizer (L : Set G))
          L (c.intermediate.pCoreIn 2) ⁅W,L⁆ ∧
        (T : Subgroup G) ⊓ c.H < (T : Subgroup G) ∧
        normalizer ((T : Subgroup G) ⊓ c.H : Set G) ≤ normalizer (L : Set G) ∧
        ∃ P : Sylow 2 c.H, (P : Subgroup c.H).map c.H.subtype = (T : Subgroup G) ⊓ c.H) ∨
      ∃ c : SourceConfiguration T L,
        generalizedFitting c.K = pCore 2 c.K ∧ ¬ IsBlock c.K) :=
  h.original_a5_source_branches_of_baumann_escape (fun hb =>
    d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2 (hXK.trans (hKB.trans hb)))

/-- At the literal Cartan consumer, normalization of Baum(T) forces the
constrained nonblock source configuration. The ordinary component has been
excluded using its actual full Sylow and original deleted-five block. -/
theorem LocalCartanWitness.original_nonblock_of_baumann_normalizes
    {H A Y X D K : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hXK : X ≤ K)
    (hKB : K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    IsAlternatingBlock L 5 ∧
    Chapter4.Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⁅W,L⁆ ∧
    ∃ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K ∧ ¬ IsBlock c.K :=
  h.original_nonblock_of_baumann_escape (fun hb =>
    d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2 (hXK.trans (hKB.trans hb)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The original 5.1.7(1) discharges the shared Baumann source input. -/
theorem rankOneBaumannNormalizerControl_source : RankOneBaumannNormalizerControl G := by
  intro T L W n h
  exact h.baumann_normalizer_le

/-- Every overgroup of the literal escaping Cartan component fails to
normalize Baum(T), by the original rank-one bound. -/
theorem LocalCartanWitness.not_le_baumann_normalizer
    {T : Sylow 2 G} {L W H A Y X D K : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D) (hXK : X ≤ K) :
    ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  intro hKB
  exact d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2
    (hXK.trans (hKB.trans h.baumann_normalizer_le))

/-- The literal maximal local Cartan construction with its Baumann premise
discharged. The independent exceptional quotient input has producer
`exceptionalLocalOvercomponentModels_source` in ExceptionalModelsSource;
the FF assembly owner supplies it alongside the subsequent FF classification. -/
theorem localCartan_maximal_models_of_exceptional_models
    (hmodels : ExceptionalLocalOvercomponentModels G)
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) :=
  localCartan_maximal_models_of_earlier_inputs hmodels
    rankOneBaumannNormalizerControl_source h hH hY d hXC

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
