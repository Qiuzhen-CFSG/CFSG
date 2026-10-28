module

public import Theory.GroupTheory.ConjugationLocalGeometry
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.SubgroupConjugation

/-!
# An order-two commutator kernel controls an abelian conjugate span

Let U be abelian, let P have order two, and suppose N(P) normalizes U.
If [U,Q] lies in P and the entire L-conjugate span of U lies in Q,
then that span is abelian. For a conjugate with a different marked point,
the commutator lies in the intersection of two distinct order-two groups;
for an unchanged point, the conjugate of U is U itself.

The source application in `SourceCompletion.CaseOne.NaturalConjugates`
uses U = U_H, P = V₁ and Q = O₂(H). It constructs a conjugate with
nontrivial literal star image in the nonabelian alternative.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A point-marked abelian group whose conjugate span stays inside its
commutator kernel has abelian span. Distinct point lines force the
conjugate commutators to vanish. -/
theorem conjugateSpan_commutative_of_line_kernel
    (U L P Q : Subgroup G) [IsMulCommutative U]
    (hP : Nat.card P = 2)
    (hN : normalizer (P : Set G) ≤ normalizer (U : Set G))
    (hc : ⁅U, Q⁆ ≤ P) (hspan : conjugateSpanBy U L ≤ Q) :
    IsMulCommutative (conjugateSpanBy U L) := by
  have hconj (l : G) (hl : l ∈ L) : ⁅U, U.conjBy l⁆ = ⊥ := by
    by_cases hp : P.conjBy l = P
    · have hlN : l ∈ normalizer (P : Set G) := mem_normalizer_iff_map_conj_eq.mpr hp
      have hu := mem_normalizer_iff_map_conj_eq.mp (hN hlN)
      change U.conjBy l = U at hu
      rw [hu]
      exact commutator_self_eq_bot_iff.mpr inferInstance
    · have hUl : U.conjBy l ≤ conjugateSpanBy U L := by
        rintro x ⟨u, hu, rfl⟩
        exact subset_closure ⟨l, hl, u, hu, rfl⟩
      have hUi : U.conjBy l⁻¹ ≤ conjugateSpanBy U L := by
        rintro x ⟨u, hu, rfl⟩
        exact subset_closure ⟨l⁻¹, L.inv_mem hl, u, hu, rfl⟩
      have hfirst : ⁅U, U.conjBy l⁆ ≤ P := (commutator_mono le_rfl (hUl.trans hspan)).trans hc
      have hsecond : ⁅U, U.conjBy l⁆ ≤ P.conjBy l := by
        have hh := map_mono (f := (MulAut.conj l).toMonoidHom)
          ((commutator_mono le_rfl (hUi.trans hspan)).trans hc)
        rw [map_commutator] at hh
        change ⁅U.conjBy l, (U.conjBy l⁻¹).conjBy l⁆ ≤ P.conjBy l at hh
        rwa [conjBy_inv', commutator_comm] at hh
      have hd : P ⊓ P.conjBy l = ⊥ := inf_eq_bot_of_card_two_of_ne P (P.conjBy l) hP
        (by change Nat.card (P.map _) = 2; rw [card_map_of_injective (MulAut.conj l).injective, hP])
        (Ne.symm hp)
      exact le_bot_iff.mp ((le_inf hfirst hsecond).trans hd.le)
  apply (conjugateSpanBy_commutative_iff U L).mpr
  apply le_centralizer_iff.mp
  apply (closure_le _).mpr
  rintro x ⟨l, hl, u, hu, rfl⟩
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hconj l hl)))
    (mem_map_of_mem _ hu)

end Subgroup
