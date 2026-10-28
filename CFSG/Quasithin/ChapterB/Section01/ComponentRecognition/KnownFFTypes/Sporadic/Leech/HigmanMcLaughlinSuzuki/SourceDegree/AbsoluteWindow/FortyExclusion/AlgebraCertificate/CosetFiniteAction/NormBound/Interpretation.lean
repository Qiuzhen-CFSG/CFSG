module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.Witness

/-!
# Interpret the sparse HS norm certificate

Each five-entry row must be a positive-word translate of a B-norm column.
Independently, its binary selectors must sum to the 78 column discrepancies.
These two finite identities put every discrepancy in the literal relation
submodule. Predecessor descent supplies coordinate reachability; the selected
family already contains zero. The resulting quotient bound feeds the original
universal-module constructor, with Schreier and kernel nilpotence still explicit.

This is a conditional assembly, not a completed finite certificate.
Source application: GM02 Proposition 5.1, HS case; Aschbacher--Smith K.4 p.457.
-/

@[expose] public section
open scoped BigOperators
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound

private theorem wordAction_single_aux {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (w : List (Fin 2)) (i : Fin n) :
    wordAction t w (Pi.single i 1) = Pi.single (w.foldr t i) 1 := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    change columnAction t s (wordAction t w (Pi.single i 1)) =
      Pi.single (t s (w.foldr t i)) 1
    rw [ih, columnAction_single]

theorem wordAction_single (w : List (Fin 2)) (i : Tables.Index) :
    wordAction Tables.transition w (Pi.single i 1) = Pi.single (pointWord w i) 1 :=
  wordAction_single_aux Tables.transition w i

private theorem wordNorm_mem_relations {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (w : List (Fin 2)) (i : Fin n) :
    wordAction t w (normAction t (Pi.single i 1)) ∈ relations t :=
  Submodule.subset_span ⟨(w, i), rfl⟩

theorem columnAction_pow_single (k : ℕ) (i : Tables.Index) :
    (columnAction Tables.transition 1 ^ k) (Pi.single i 1) =
      Pi.single ((Tables.transition 1)^[k] i) 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, columnAction_single,
      Function.iterate_succ_apply']

/-- Every certified geometric row belongs to the actual norm-relation span. -/
theorem rowVector_mem_relations (hg : SeedGeometry) (r : Row) :
    rowVector r ∈ relations Tables.transition := by
  have he : rowVector r = wordAction Tables.transition (conjugator (rowStep r))
      (normAction Tables.transition (Pi.single (rowStart r) 1)) := by
    rw [rowVector, normAction, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [columnAction_pow_single, wordAction_single, hg r k]
  rw [he]
  exact wordNorm_mem_relations Tables.transition (conjugator (rowStep r)) (rowStart r)

theorem combinationVector_mem_relations (hg : SeedGeometry) (s : Fin 2) (j : Fin 39) :
    combinationVector s j ∈ relations Tables.transition := by
  apply Submodule.sum_mem
  intro r _
  split_ifs
  · exact rowVector_mem_relations hg r
  · exact Submodule.zero_mem _

/-- The sparse parity and row geometry discharge the literal column relations. -/
theorem columnVector_mem_relations (hg : SeedGeometry) (hr : RowIdentities)
    (s : Fin 2) (j : Fin 39) : columnVector s j ∈ relations Tables.transition := by
  rw [hr s j]
  exact combinationVector_mem_relations hg s j

noncomputable def selectedSpan : Submodule (ZMod 2) (NormQuotient Tables.transition) :=
  Submodule.span (ZMod 2)
    (Set.range fun j => (relations Tables.transition).mkQ (Pi.single (selected j) 1))

theorem seed_mem_selectedSpan :
    (relations Tables.transition).mkQ (Pi.single 0 1) ∈ selectedSpan := by
  apply Submodule.subset_span
  exact ⟨0, congrArg (fun i => (relations Tables.transition).mkQ (Pi.single i 1)) selected_zero⟩

theorem selectedVector_mem_selectedSpan (c : ℕ) :
    (relations Tables.transition).mkQ (selectedVector c) ∈ selectedSpan := by
  rw [selectedVector, map_sum]
  apply Submodule.sum_mem
  intro j _
  split_ifs
  · exact Submodule.subset_span ⟨j, rfl⟩
  · simpa only [map_zero] using selectedSpan.zero_mem

theorem column_mem_selectedSpan (hg : SeedGeometry) (hr : RowIdentities)
    (s : Fin 2) (j : Fin 39) :
    (relations Tables.transition).mkQ
      (Pi.single (Tables.transition s (selected j)) 1) ∈ selectedSpan := by
  have he : (relations Tables.transition).mkQ
        (Pi.single (Tables.transition s (selected j)) 1) =
      (relations Tables.transition).mkQ (selectedVector (columnCode s j)) :=
    (Submodule.Quotient.eq _).mpr (columnVector_mem_relations hg hr s j)
  rw [he]
  exact selectedVector_mem_selectedSpan _

/-- Once the three independent finite certificates are supplied, 39 coordinates
span the original quotient. This is only their mathematical assembly. -/
theorem finrank_quotient_le_of_certificates (hg : SeedGeometry) (hr : RowIdentities)
    (hc : Reachable) :
    Module.finrank (ZMod 2) (NormQuotient Tables.transition) ≤ 39 := by
  apply finrank_quotient_le_of_columns Tables.transition 0 selected
  · intro i
    obtain ⟨w, hw⟩ := hc i
    exact ⟨w, by rw [wordAction_single, hw]⟩
  · exact seed_mem_selectedSpan
  · exact column_mem_selectedSpan hg hr

theorem finrank_quotient_lt_of_certificates (hg : SeedGeometry) (hr : RowIdentities)
    (hc : Reachable) :
    Module.finrank (ZMod 2) (NormQuotient Tables.transition) < 40 :=
  lt_of_le_of_lt (finrank_quotient_le_of_certificates hg hr hc) (by decide)

/-- Actual consumer of this finite calculation. The unrelated Schreier and
r-fold universal-kernel premises are retained exactly as in of_table_bound. -/
noncomputable def of_sparse_certificates (hg : SeedGeometry) (hr : RowIdentities)
    (hc : Reachable) (hs : SchreierCondition) (r : ℕ)
    (hk : ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, cosetNormRepresentation.asAlgebraHom x = 0) →
        xs.prod ∈ fiveNormIdeal) : NormCertificate :=
  of_table_bound hs (finrank_quotient_lt_of_certificates hg hr hc) r hk

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound

