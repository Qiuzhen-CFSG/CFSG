module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComponentRecognition.Data
import Mathlib.Tactic.FinCases

/-!
# Kernel checks for the paired HS/A₆ word enumeration

Left multiplication by each generator or its inverse sends every word row to
the indexed row in both permutation representations. Decoding three HS images
and four six-letter images recovers the row index. Thus both projections are
injective on the enumeration. All computations use `decide +kernel`.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m.
The candidate words and transition data are retained in `Data` and `source/`.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComponentRecognition
open Sporadic.LeechRelated.HS Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

private def chunkRow (b : Fin 10) (r : Fin 36) : Fin 360 :=
  ⟨36 * b.val + r.val, by omega⟩

private theorem hsStep0 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 0 r)).1) x =
      inclusion (row (next i (chunkRow 0 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep1 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 1 r)).1) x =
      inclusion (row (next i (chunkRow 1 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep2 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 2 r)).1) x =
      inclusion (row (next i (chunkRow 2 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep3 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 3 r)).1) x =
      inclusion (row (next i (chunkRow 3 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep4 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 4 r)).1) x =
      inclusion (row (next i (chunkRow 4 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep5 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 5 r)).1) x =
      inclusion (row (next i (chunkRow 5 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep6 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 6 r)).1) x =
      inclusion (row (next i (chunkRow 6 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep7 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 7 r)).1) x =
      inclusion (row (next i (chunkRow 7 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep8 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 8 r)).1) x =
      inclusion (row (next i (chunkRow 8 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep9 : ∀ i : Fin 4, ∀ r : Fin 36, ∀ x : Fin 100,
    inclusion ((letter i * row (chunkRow 9 r)).1) x =
      inclusion (row (next i (chunkRow 9 r))).1 x := by
  apply Certificate.allFin
  decide +kernel

private theorem hsStep : ∀ i : Fin 4, ∀ r : Fin 360, ∀ x : Fin 100,
    inclusion ((letter i * row r).1) x = inclusion (row (next i r)).1 x := by
  have h (b : Fin 10) (r : Fin 36) (i : Fin 4) (x : Fin 100) :
      inclusion ((letter i * row (chunkRow b r)).1) x =
        inclusion (row (next i (chunkRow b r))).1 x := by
    fin_cases b
    · exact hsStep0 i r x
    · exact hsStep1 i r x
    · exact hsStep2 i r x
    · exact hsStep3 i r x
    · exact hsStep4 i r x
    · exact hsStep5 i r x
    · exact hsStep6 i r x
    · exact hsStep7 i r x
    · exact hsStep8 i r x
    · exact hsStep9 i r x
  intro i r x
  have hr : chunkRow ⟨r.val / 36, by omega⟩ ⟨r.val % 36, by omega⟩ = r := by
    apply Fin.ext
    simp [chunkRow, Nat.div_add_mod]
  simpa only [hr] using h ⟨r.val / 36, by omega⟩ ⟨r.val % 36, by omega⟩ i x

private theorem sixStep : ∀ i : Fin 4, ∀ r : Fin 360, ∀ x : Fin 6,
    (letter i * row r).2.val x = (row (next i r)).2.val x := by
  apply Certificate.allFin
  decide +kernel

/-- Genuine paired multiplication identities, in both representations. -/
theorem step (i : Fin 4) (r : Fin 360) : letter i * row r = row (next i r) := by
  apply Prod.ext
  · exact inclusion_injective (Equiv.ext (hsStep i r))
  · exact Subtype.ext (Equiv.ext (sixStep i r))

/-- The first row is the identity in the paired group. -/
theorem row_zero : row 0 = 1 := rfl

private theorem hs_decode : ∀ r : Fin 360,
    decodeHS (hsKey (inclusion (row r).1)) = r.val := by
  apply Certificate.allFin
  decide +kernel

private theorem six_decode : ∀ r : Fin 360,
    decodeSix (sixKey (row r).2.val) = r.val := by
  apply Certificate.allFin
  decide +kernel

/-- The HS projection distinguishes all 360 word rows. -/
theorem hs_injective : Function.Injective (fun r => (row r).1) := by
  intro r s h
  apply Fin.ext
  have he := congrArg (fun g => decodeHS (hsKey (inclusion g))) h
  simpa only [hs_decode] using he

/-- The six-letter projection distinguishes all 360 word rows. -/
theorem six_injective : Function.Injective (fun r => (row r).2) := by
  intro r s h
  apply Fin.ext
  have he := congrArg (fun g : A6 => decodeSix (sixKey g.val)) h
  simpa only [six_decode] using he

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComponentRecognition
