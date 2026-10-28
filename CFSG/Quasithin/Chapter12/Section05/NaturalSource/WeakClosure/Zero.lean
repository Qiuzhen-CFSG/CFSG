module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Geometry
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Symmetry
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Bounds
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointSylow
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.GenerationOne

/-!
# Zeroth exterior weak closure after the parameter calculation

Under the numerical conclusions of 12.5.6, the literal exterior A₃
calculation gives the commutator V₆ and reverse normalization. Sylow
conjugacy inside N_G(V) then supplies the symmetry step, and G₆≤M together
with the original TI property excludes every noncentralizing conjugate in T.
Thus W₀ centralizes V, w is positive, and N_G(W₀)≤M.

The final two applications discharge the W₀ premises in the existing point
fusion and generation-one consumers. Their independent point-core and W₁
inputs remain explicit in this module. Zero.Parameters proves the numerical
source argument 12.5.6 and applies it here; Zero.Consumers supplies the
remaining generation-one inputs from the independent point-core containment.

Source: Aschbacher--Smith, 12.5.6--7, 12.5.9 and 12.5.11(1), pp.819--821.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The complete deduction of 12.5.7 from 12.5.6 and the earlier local inputs. -/
theorem zero_clauses_of_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ s.marking.M := by
  have hw := zero_centralizes_of_symmetric_commutators s h structural hG₆
    (fun g hg hn => s.conjugate_three_geometry g hg hn hs hr)
  exact ⟨hw, zero_bounds_of_centralizes s h hw⟩

/-- The original point-fusion consumer needs no additional weak-closure premise. -/
theorem pointControl_of_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2) : PointControl s.marking := by
  obtain ⟨hw, _, hn⟩ := zero_clauses_of_parameters s h structural hG₆ hr hs
  exact pointControl_of_source_weakClosure s h structural hcore hw hn

/-- The original H-star generation argument now retains only its W₁ input. -/
theorem generation_ne_one_of_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3)
    (hW₁ : indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (s.marking.Vi 6 : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    generationParameter H ≠ 1 := by
  have hn := (zero_clauses_of_parameters s h structural hG₆ hr hs).2.2
  exact generation_ne_one_of_V₆_fixed s.marking hs hn hG₆ hW₁ hH

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
