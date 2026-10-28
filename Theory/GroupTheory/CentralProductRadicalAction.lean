module
public import Theory.GroupTheory.CentralProductMovedProjection
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.ThreeSubgroups

/-!
# Radical action on a perfect central-product projection

A prime subgroup acting trivially modulo the core of a subgroup of a central
product acts trivially modulo the core of its perfect coordinate projection.
Project the original core to the coordinate, then apply the relative
three-subgroups lemma to remove the other commuting coordinate. Both factors
must be preserved by the prime subgroup; no disjointness is required.

Source: the projection step in Aschbacher–Smith C.3.2, printed p.149.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The original radical commutator bound passes to its perfect coordinate. -/
theorem perfect_projection_radical_commutator
    (A P Q R : Subgroup G) [Group.IsPerfect P]
    (hc : P ≤ centralizer (Q : Set G))
    (hAP : A ≤ P ⊔ Q) (hPA : P ≤ A ⊔ Q)
    (hRA : R ≤ normalizer (A : Set G))
    (hAR : A ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (P : Set G))
    (hRQ : R ≤ normalizer (Q : Set G))
    (hp : IsPGroup p R) : ⁅P,R⁆ ≤ P.pCoreIn p := by
  have hAQ : A ≤ normalizer (Q : Set G) := hAP.trans
    (sup_le (hc.trans (centralizer_le_normalizer _)) Q.le_normalizer)
  have hAPn : A ≤ normalizer (P : Set G) := hAP.trans
    (sup_le P.le_normalizer ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)))
  have hAU : A ≤ normalizer (A.pCoreIn p : Set G) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore p A))
  obtain ⟨W,hWP,hWp,hAW,hUW⟩ := exists_prime_projection_of_central_product
    Q P (A.pCoreIn p) A (le_centralizer_iff.mp hc)
      (isPGroup_pCoreIn p A) ((pCoreIn_le p A).trans (hAP.trans (by rw [sup_comm])))
      hAQ hAPn hAU
  have hQW : Q ≤ centralizer (W : Set G) :=
    (le_centralizer_iff.mp hc).trans (centralizer_le hWP)
  have hPW : P ≤ normalizer (W : Set G) := hPA.trans
    (sup_le hAW (hQW.trans (centralizer_le_normalizer _)))
  have hWcore : W ≤ P.pCoreIn p := le_pCoreIn_of_normalizes hWp hWP hPW
  have hUPQ : A.pCoreIn p ≤ P.pCoreIn p ⊔ Q :=
    hUW.trans (sup_le le_sup_right (hWcore.trans le_sup_left))
  have hcomm : ⁅A,R⁆ ≤ A.pCoreIn p := le_pCoreIn_of_normalizes
    (hp.to_le (le_normalizer_iff_commutator_le_right.mp hAR))
    (le_normalizer_iff_commutator_le_left.mp hRA) (normalizer_commutator_ge_left A R)
  have hPU : P ≤ normalizer (P.pCoreIn p : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pCore p P))
  have hQU : Q ≤ normalizer (P.pCoreIn p : Set G) :=
    ((le_centralizer_iff.mp hc).trans (centralizer_le (pCoreIn_le p P))).trans
      (centralizer_le_normalizer _)
  have hn : P ⊔ Q ≤ normalizer ((P.pCoreIn p ⊔ Q : Subgroup G) : Set G) :=
    (le_inf (sup_le hPU hQU)
      (sup_le (hc.trans (centralizer_le_normalizer _)) Q.le_normalizer)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hPR : ⁅P,R⁆ ≤ P.pCoreIn p ⊔ Q :=
    (commutator_mono hPA le_rfl).trans
      (commutator_sup_le_of_relative_normal (P ⊔ Q) A Q R (P.pCoreIn p ⊔ Q)
        hn hAP le_sup_right (hcomm.trans hUPQ)
        ((le_normalizer_iff_commutator_le_left.mp hRQ).trans le_sup_right))
  have hdouble : ⁅⁅P,R⁆,P⁆ ≤ P.pCoreIn p :=
    commutator_le_of_le_sup_centralizing ⁅P,R⁆ P (P.pCoreIn p) Q
      (hPR.trans (by rw [sup_comm])) ((le_centralizer_iff.mp hc).trans (centralizer_le (pCoreIn_le p P)))
      (le_centralizer_iff.mp hc) hPU
  have hRU : R ≤ normalizer (P.pCoreIn p : Set G) := hRP.trans
    (normalizer_le_normalizer_characteristic_image P (pCore p P))
  have hh := commutator_commutator_le_of_rotate_of_le_normalizer hPU hPU hRU
    hdouble (by simpa only [commutator_comm R P] using hdouble)
  rwa [P.commutator_eq_self] at hh
end Theory.GroupTheory
