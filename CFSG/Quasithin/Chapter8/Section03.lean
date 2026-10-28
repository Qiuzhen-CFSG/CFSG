module

public import CFSG.Quasithin.Chapter8.Section03.Fusion
public import CFSG.Quasithin.Chapter8.Section03.PointFusion

/-!
# Eliminating L₃(2) wr 2 on its nine-dimensional tensor module

Source: Aschbacher--Smith, combined manuscript (1 March 2004), §8.3,
printed pp.723--727, PDF pp.740--744. Theorem 8.3.1 is under the full
Fundamental Setup and Hypotheses 7.0.2 and 7.3.1, with the actual tensor
representation, not merely an isomorphism of the acting groups.

The result below proves the weak-closure deduction in 8.3.14. Its numerical,
tensor-geometric and fusion inputs remain explicit. The source elimination
is not yet proved: it needs the centralizer analysis 8.3.7--12 (carrying the
additional Held case until its genuine local and generation arguments
exclude it), the FSU fusion result 3.2.10(6), and E.3.16/19 for the final
contradiction. In particular no elimination theorem is inferred from this
conditional result alone.
-/

public section

namespace CFSG.Quasithin.Chapter8.Section03

open Subgroup ChapterE

/-- The deduction in 8.3.14 from the genuine r bound of 8.3.11, the
S₁ × S₂ hyperplane geometry and the intersection-fusion conclusion of
8.3.13. Each remaining input must be constructed in the source assembly. -/
theorem lemma_8_3_14_of_hyperplane_geometry
    {G : Type*} [Group G] {V S : Subgroup G} {z : G}
    (hSN : S ≤ normalizer (V : Set G))
    (hr : (3 : ℕ∞) < globalR V)
    (hgeometry : ∀ A ∈ gamma V S 2, ¬ A ≤ centralizer (V : Set G) →
      HasFusedHyperplane V A z)
    (hfusion : ∀ (g x : G), x ∈ V →
      x ∈ V.map (MulAut.conj g).toMonoidHom → IsConj x z →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    indexedWeakClosure V S 2 ≤ centralizer (V : Set G) :=
  weakClosure_le_centralizer_of_fused_hyperplanes hSN hr hgeometry hfusion

/-- Composition of 8.3.13 with the weak-closure deduction. The remaining
source obligations are the tensor hyperplane witness, r > 3, 8.3.12 and
the two genuine FSU fusion consequences. -/
theorem weakClosure_two_le_centralizer_of_core_and_geometry
    {G : Type*} [Group G] [Finite G] (D : CentralizerSetup G) (V : Subgroup G)
    (hz : orderOf D.z = 2) (hzV : D.z ∈ V)
    (hcore : V ≤ D.Gz.pCoreIn 2)
    (hSN : D.S ≤ normalizer (V : Set G))
    (hr : (3 : ℕ∞) < globalR V)
    (hgeometry : ∀ A ∈ gamma V D.S 2, ¬ A ≤ centralizer (V : Set G) →
      HasFusedHyperplane V A D.z)
    (hcontrol : ∀ x ∈ V, IsConj x D.z →
      ∃ m ∈ normalizer (V : Set G), (MulAut.conj m) x = D.z)
    (hcoreFusion : ∀ U : Subgroup G, U ≤ V →
      V ≤ (normalizer (U : Set G)).pCoreIn 2 →
      ∀ g : G, U ≤ V.map (MulAut.conj g).toMonoidHom →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    indexedWeakClosure V D.S 2 ≤ centralizer (V : Set G) :=
  lemma_8_3_14_of_hyperplane_geometry hSN hr hgeometry
    (lemma_8_3_13_of_core_and_FSU_fusion D V hz hzV hcore hcontrol hcoreFusion)

end CFSG.Quasithin.Chapter8.Section03
