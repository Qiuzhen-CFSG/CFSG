module
public import CFSG.Quasithin.Chapter10.SourceNonnormalA5CoveringCounterexample
public import CFSG.Quasithin.ChapterC.Section04.A5ConstrainedSelection

/-!
# The constrained remainder of the original A₅ covering counterexample

Retain the pushed subgroup J, maximal two-local H, prescribed Sylow S,
literal component LH and its quotient marking inherited from L. The
contained-Fitting and complete ordinary cases are discharged. The selected
escaping C-component is constrained, and its actual star quotient belongs
to one of the four displayed remaining model families.

This is the original consumer of the completed ordinary dispatcher and
finite constrained rows. The remaining rank-one, degree-three, large G₂
and A₅ normalizer geometry is kept explicit, with its actual radical.
Source: Aschbacher–Smith 4.2.12–13, pp.610–611, using C.4.8, pp.153–154,
in the A₅ setup of 10.2, printed p.744.
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
theorem source_a5_covering_counterexample_constrained_remainder
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
          generalizedFitting K = pCore 2 K ∧
          ((∃ F : BinaryField, Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2)
              (K.map H.subtype) ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) ∨
           (∃ F : BinaryField, Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2)
              (K.map H.subtype) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)) ∨
           (∃ F : BinaryField, 1 < F.degree ∧ Nonempty (starImage (K.map H.subtype)
              (J.pCoreIn 2) (K.map H.subtype) ≃* Atlas.G2.Model F.Carrier)) ∨
           Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
              alternatingGroup (Fin 5))) := by
  obtain ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,_,_,eH,heH⟩ :=
    source_a5_covering_counterexample D e hn hIM hcover hcore horbit hnot
  exact ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,eH,heH,
    hC28.nonnormal_a5_constrained_remainder hlt eH hnorm⟩

end CFSG.Quasithin.Chapter10
