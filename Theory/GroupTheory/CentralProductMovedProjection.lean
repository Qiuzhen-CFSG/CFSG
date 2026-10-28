module

public import Theory.GroupTheory.CComponent.OrdinaryProjection

/-!
# A perfect projection with noncentral prime core

Let a perfect subgroup of a central product contain a prime subgroup equal
to its commutator with the perfect subgroup. If that prime subgroup has a
nontrivial projection to the first factor, the perfect coordinate projection
has noncentral prime core. Both projections are taken through the actual
multiplication map, so a central intersection of the factors is allowed.

This isolates the local subgroup obstruction in Aschbacher--Smith C.3.3,
printed p.149. The construction also retains the stabilizers used in C.3.2.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A noncentral moved prime subgroup forces a noncentral prime core in the
actual perfect coordinate projection. -/
theorem exists_perfect_projection_with_noncentral_core
    (K C A V : Subgroup G) [Group.IsPerfect A]
    (hc : K ≤ centralizer (C : Set G)) (hA : A ≤ K ⊔ C)
    (hVA : V ≤ A) (hV : IsPGroup p V) (hmoved : V = ⁅V,A⁆)
    (hnc : ¬ V ≤ C) :
    ∃ P Q : Subgroup G, P ≤ K ∧ Q ≤ C ∧ Group.IsPerfect P ∧ Group.IsPerfect Q ∧
      A ≤ P ⊔ Q ∧ P ≤ A ⊔ Q ∧ ⁅P.pCoreIn p,P⁆ ≠ ⊥ ∧
      (∀ B : Subgroup G, B ≤ normalizer (K : Set G) →
        B ≤ normalizer (C : Set G) → B ≤ normalizer (A : Set G) →
        B ≤ normalizer (P : Set G)) := by
  obtain ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hN⟩ :=
    exists_perfect_projections_of_central_product K C A hc hA
  have hPQ : P ≤ centralizer (Q : Set G) :=
    hPK.trans (hc.trans (centralizer_le hQC))
  have hAK : A ≤ normalizer (K : Set G) := hA.trans
    (sup_le K.le_normalizer ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)))
  have hAC : A ≤ normalizer (C : Set G) := hA.trans
    (sup_le (hc.trans (centralizer_le_normalizer _)) C.le_normalizer)
  have hANP : A ≤ normalizer (P : Set G) := hN A hAK hAC A.le_normalizer
  have hANQ : A ≤ normalizer (Q : Set G) := hAP.trans
    (sup_le (hPQ.trans (centralizer_le_normalizer _)) Q.le_normalizer)
  have hANV : A ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hmoved.symm.le
  obtain ⟨W,hWP,hWp,hAW,hVW⟩ :=
    exists_prime_projection_of_central_product Q P V A
      (le_centralizer_iff.mp hPQ) hV (hVA.trans (hAP.trans (by rw [sup_comm])))
      hANQ hANP hANV
  have hQW : Q ≤ centralizer (W : Set G) :=
    (le_centralizer_iff.mp hPQ).trans (centralizer_le hWP)
  have hPW : P ≤ normalizer (W : Set G) := hPA.trans
    (sup_le hAW (hQW.trans (centralizer_le_normalizer _)))
  have hWcore : W ≤ P.pCoreIn p := le_pCoreIn_of_normalizes hWp hWP hPW
  refine ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,?_,hN⟩
  intro he
  have hWCP : W ≤ centralizer (P : Set G) :=
    hWcore.trans (commutator_eq_bot_iff_le_centralizer.mp he)
  have hWCA : W ≤ centralizer (A : Set G) := le_centralizer_iff.mp
    (hAP.trans (sup_le (le_centralizer_iff.mp hWCP) hQW))
  apply hnc
  rw [hmoved]
  exact (commutator_le_of_le_sup_centralizing V A Q W
    (hVW.trans (by rw [sup_comm])) (le_centralizer_iff.mp hQW) hWCA hANQ).trans hQC

end Theory.GroupTheory
