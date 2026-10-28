module
public import CFSG.Quasithin.Chapter10.SourceNonnormalA5CoveringCounterexample
public import CFSG.Quasithin.ChapterC.Section04.A5ComponentSelection

/-!
# The remaining component in the original A₅ covering counterexample

Retain the original pushed subgroup J, maximal two-local H, prescribed
Sylow subgroup S, literal component LH and its quotient marking inherited
from L. The completed C.2.13 branch forces an escaping component in H;
it is ordinary or belongs to the actual C.2.7 constrained star catalogue.
The constrained symplectic row has already been excluded by the literal
span-action five-rank contradiction.

This is the original consumer of the action-kernel theorem. The unclosed
ordinary and constrained catalogue rows remain explicit in its conclusion.
Source: Aschbacher–Smith 4.2.12–13, printed pp.610–611, using C.4.8,
printed pp.153–154, in the A₅ setup of 10.2, printed p.744.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section02.Unitary
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual marked covering counterexample lies in a remaining component branch. -/
theorem source_a5_covering_counterexample_component_remainder
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L)
    (hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      PushLE (localOrbit T L) I J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ D.maximalLocal < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ D.maximalLocal)
        LH (J.pCoreIn 2)
        (fullModule (localOrbit T L)
          ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
            (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
      ¬ H ⊓ D.maximalLocal ≤ normalizer (LH : Set G) ∧
      ∃ eH : (LH ⧸ pCore 2 LH) ≃* alternatingGroup (Fin 5),
        (∀ x : LH, eH (QuotientGroup.mk' (pCore 2 LH) x) =
          e (QuotientGroup.mk' (pCore 2 L)
            ⟨x.val, ((map_subtype_le _).trans inf_le_left) x.property⟩)) ∧
        ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
          ¬ K ≤ (H ⊓ D.maximalLocal).subgroupOf H ∧
          (IsComponent H K ∨
            (generalizedFitting K = pCore 2 K ∧
              ChapterC.C27Source.StarModels.Model
                (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)) ∧
              ∀ F : BinaryField, 1 < F.degree →
                ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2)
                  (K.map H.subtype) ≃* Sp F.Carrier))) := by
  obtain ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,_,_,eH,heH⟩ :=
    source_a5_covering_counterexample D e hn hIM hcover hcore horbit hnot
  exact ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,eH,heH,
    hC28.nonnormal_a5_component_remainder hlt eH hnorm⟩

end CFSG.Quasithin.Chapter10
