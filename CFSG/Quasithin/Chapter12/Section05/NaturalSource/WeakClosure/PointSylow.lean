module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointSylow.MarkedOrbit
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointFusion
public import Theory.GroupTheory.PointSylowRechoice

/-!
# The Sylow-aligned nonsingular point of 12.5.9

The nonsingular orbit has length 868 among 1024 vectors. Thus its orbit
under L is preserved by N_G(L) ∩ N_G(V), acting by literal conjugation.
Choose a Sylow of the point stabilizer and extend it to that acting group;
Sylow conjugacy aligns it with the original T, and the large-orbit argument
allows the point transporter to lie in L. The two-part of 868 is four.
The source TI property makes this point stabilizer the full C_M(z′ˡ).

This constructs PointSylowGeometry without any W₀ input and preserves the
canonical z′. The final application discharges the local geometry premise
of PointControl. Only the genuine earlier structural theorem 12.2.2 remains
explicit; its producer is qt-d-1222-source. The W₀ and point-core bounds in
the PointControl application belong to the separate weak-closure owners.

Source: Aschbacher--Smith, 12.5.9(1), printed p.821, using 12.5.5(3), p.819.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- Construct the local Sylow choice from the original source hypotheses and
its earlier structural theorem, retaining the unchanged canonical point. -/
theorem pointSylowGeometry_nonempty (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    Nonempty (PointSylowGeometry s) := by
  have hTI := ((structural L h).2.2 V D).2.2.1
  obtain ⟨l, hindex, hlocal⟩ := exists_point_centralizer_sylow_in_component T L V
    (structural L h).1 (le_sup_right.trans s.normalizes) D.normalizes hTI
    ⟨s.marking.zPrime, s.marking.zPrime_mem⟩ s.marking.zPrime_ne_one (by
      rw [s.marking.card_module, s.marking.pointCentralizer_relIndex]; decide)
  refine ⟨⟨l, ?_, hlocal⟩⟩
  change (pointSylow s l).relIndex (T : Subgroup G) =
    2 ^ ((centralizer ({s.marking.zPrime} : Set G)).relIndex L).factorization 2 at hindex
  rw [s.marking.pointCentralizer_relIndex] at hindex
  have hf : (868 : ℕ).factorization 2 = 2 := by
    rw [show 868 = 2 ^ 2 * 217 from rfl,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 217)]
  exact hindex.trans (by rw [hf]; rfl)

/-- The point-fusion consumer now requires only the independent point-core
and zeroth weak-closure conclusions, with its local Sylow choice discharged. -/
theorem pointControl_of_source_weakClosure (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      s.marking.M) : PointControl s.marking := by
  obtain ⟨geometry⟩ := pointSylowGeometry_nonempty s h structural
  exact pointControl_of_weakClosure s geometry hcore hW hN

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
