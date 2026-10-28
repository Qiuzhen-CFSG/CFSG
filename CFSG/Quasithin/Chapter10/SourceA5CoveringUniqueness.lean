module
public import CFSG.Quasithin.Chapter10.SourceNonnormalA5CoveringCounterexample
public import CFSG.Quasithin.ChapterC.Section04.A5Normality

/-!
# Covering uniqueness in the original A₅ configuration

The original covering counterexample constructs the genuine C.2.8
configuration, strict local containment, and the A₅ marking of its
literal component `(L ∩ H)^∞`. The completed specialized C.4.8 normality
theorem contradicts the nonnormality of that same component. Thus the
original covering subgroup has the prescribed unique maximal overgroup.

Source: Aschbacher–Smith 4.2.12–13, printed pp.610–611, and the A₅ setup
of 10.2, p.744, using C.4.8, pp.153–154 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_covering_uniqueness
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L) :
    UniqueMaximalOvergroup I D.maximalLocal := by
  by_contra hnot
  obtain ⟨J,H,S,hIJ,hH,hJH,hlt,hC28,hnorm,_,_,eH,heH⟩ :=
    source_a5_covering_counterexample D e hn hIM hcover hcore horbit hnot
  exact hnorm (hC28.normalizes_of_a5_quotient hlt eH)

end CFSG.Quasithin.Chapter10
