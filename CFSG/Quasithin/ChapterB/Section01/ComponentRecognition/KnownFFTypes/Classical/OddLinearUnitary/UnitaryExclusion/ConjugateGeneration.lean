module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceInputs
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Inner
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Outer
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.Representation.BinaryIrreducibleCentralizer

/-!
# Central-cover assembly of the PSU₃ conjugate bounds

Conjugation on the specified central quotient gives the actual model actor.
Perfectness makes the action kernel the centralizer of L, and binary Schur
excludes a nontrivial involution in that kernel. Since L is F*(G), it contains
its centralizer. The finite-tuple lifting theorem therefore turns model
conjugators into ambient conjugators generating a subgroup containing all
of L, including its center and allowing outer actors.

The concrete root-group calculations supply five conjugates for both inner
and outer involutions above parameter five. The actual maximal A₇ and S₇
models supply four at five; padding also gives five there. Applying these
three proved estimates discharges every model-generation premise of
`sourceConjugateBounds`. The conditional assembly remains available.

Sources: Aschbacher–Smith K.2, printed p.453; Guralnick–Malle,
*Classification of 2F-modules I*, §2 and Proposition 4.3, manuscript pp.4
and 10–11. Final parameter assembly remains in `SourceReduction`.
-/

public section
open Subgroup Theory.GroupTheory Representation
open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
universe u v

/-- Model generation lifts to every source involution with the same literal conjugate count. -/
theorem source_conjugates_of_projective_bound
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    {p : ℕ} (h : SourceHypotheses ρ L p)
    {S : Type*} [Group S] (e : L ⧸ center L ≃* S) {n : ℕ}
    (hgen : ∀ a : MulAut S, a ≠ 1 → a ^ 2 = 1 → MulAut.HasInnerConjugateCover a n) :
    ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin n → G, L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let : L.Normal := h.fitting ▸ (inferInstance : (generalizedFitting G).Normal)
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hc : centralizer (L : Set G) ≤ L := by
    rw [← h.fitting]
    exact Theory.GroupTheory.centralizer_generalizedFitting_le G
  let f := MulAut.centralQuotientConjugation L e
  intro t ht ht2
  have hft : f t ≠ 1 := by
    intro he
    apply ht
    apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ L h.faithful ht2
    rw [← MulAut.centralQuotientConjugation_ker L e]
    exact he
  have hft2 : f t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  obtain ⟨s, hs⟩ := hgen (f t) hft hft2
  exact MulAut.lift_conjugate_generation L e hc t s hs

/-- Conditional source assembly from the three concrete generation bounds. -/
theorem sourceConjugateBounds_of_model_bounds
    (hinner : InnerFiveBound.{0}) (houter : OuterFiveBound.{0})
    (hfour : FourBoundAtFive.{0}) : SourceConjugateBounds.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ p h hp
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := h.quotient
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.symm.isSimpleGroup
  constructor
  · apply source_conjugates_of_projective_bound ρ L h e
    intro a ha ha2
    by_cases hp5 : p = 5
    · subst p
      exact (hfour J hcard hconj a ha ha2).mono (by decide)
    · have hlarge : 5 < p := by
        obtain ⟨k, hk⟩ := h.odd
        omega
      by_cases hi : ∃ s, a = MulAut.conj s
      · exact hinner J h.prime h.odd hlarge hcard hconj a ha ha2 hi
      · exact houter J h.prime h.odd hlarge hcard hconj a ha ha2 hi
  · intro hp5
    subst p
    exact source_conjugates_of_projective_bound ρ L h e (hfour J hcard hconj)

/-- Every nonidentity source involution has five ambient conjugates whose
closure contains the entire quasisimple component; at parameter five, four
suffice. Both inner and outer actors are included, with all concrete model
generation premises discharged. -/
theorem sourceConjugateBounds : SourceConjugateBounds.{u, v} :=
  sourceConjugateBounds_of_model_bounds innerFiveBound outerFiveBound fourBoundAtFive

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
