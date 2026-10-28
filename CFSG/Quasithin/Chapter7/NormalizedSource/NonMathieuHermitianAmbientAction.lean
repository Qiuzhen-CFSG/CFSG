module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianJankoComparison
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Action
public import Theory.GroupTheory.AmalgamLocalCores
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.Comparison

/-!
# Nontriviality of the original odd actor on an escaping component

Suppose the original odd section actor acts trivially on the simple section
of a T-normalized component with quasisimple two-core quotient. Perfect
central descent puts its commutators in the full two-core. The original
odd-actor closure comparison then puts the whole component in N_G(L).
Consequently an escaping component has an actor whose simple-section action
has the original prime order.

The proof-only import isolates the comparison already proved in the Mathieu
implementation. Its unrelated chapter exports are kept private because they
collide with the rank-one implementation used by the Hermitian consumer.
No public boundary of either implementation is changed.
Source: the last paragraph of Aschbacher--Smith 4.4.3, printed p.623,
as used in 8.2.7, printed p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- An escaping component normalized by the original T must admit a
nontrivial simple-section action of the same original odd section actor. -/
theorem sourceOrbit_hermitian_oddActor_nontrivial_simple_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ sectionCentralizer L)
    (C : Subgroup G) (Q : Subgroup C) [Q.Normal]
    [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (hTQ : (T : Subgroup G) ≤ normalizer (Q.map C.subtype : Set G))
    (hAC : A ≤ C) (hAQ : A ≤ normalizer (Q.map C.subtype : Set G))
    (hQout : ¬ Q.map C.subtype ≤ normalizer (L : Set G)) :
    ∃ a : A, orderOf (simpleAction Q (inclusion hAC a)) = p := by
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have hntriv : ¬ ∀ a : A, simpleAction Q (inclusion hAC a) = 1 := by
    intro ht
    have hc : ⁅A.subgroupOf C,Q⁆ ≤ Q.pCoreIn 2 :=
      commutator_le_of_trivial_simpleAction Q (A.subgroupOf C)
        (fun a => ht ⟨a,a.property⟩)
    have hcG := map_mono (f := C.subtype) hc
    rw [map_commutator,map_subgroupOf_eq_of_le hAC,
      ←AmalgamLocalCores.pCoreIn_map_of_injective 2 C.subtype C.subtype_injective] at hcG
    have ho : Odd (Nat.card A) := by
      obtain ⟨n,hn⟩ := hAe.isPGroup.exists_card_eq
      rw [hn]
      exact (hp.odd_of_ne_two (by omega)).pow
    exact hQout (sourceOrbit_oddActor_comparison D h A hne
      hA
      ho (Q.map C.subtype) hTQ ((le_sectionCentralizer_iff _ _).mpr ⟨hAQ,hcG⟩))
  obtain ⟨a,ha⟩ := not_forall.mp hntriv
  refine ⟨a,orderOf_eq_prime ?_ ha⟩
  rw [←map_pow]
  have hpA : (inclusion hAC a)^p=1 := by
    rw [←map_pow]
    have ha' : a^p=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
    rw [ha',map_one]
  rw [hpA,map_one]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
