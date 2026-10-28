module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.FiniteQuotient

/-!
# Small spanning columns in the finite HS norm quotient

Word translates of the five-norm columns form a generator-invariant submodule.
Thus both table operators descend to the quotient. A finite family which spans
the seed and is stable under the two descended operators spans every reachable
coordinate. If all coordinates are reachable, its size bounds the quotient's
finrank. No large matrix inverse or full echelon-form certificate is required.

`of_quotient_columns` feeds these finite conditions into the actual universal
module consumer, keeping the actual-carrier comparison and the independent
kernel-nilpotence premise explicit.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS case; Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
open scoped BigOperators
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
noncomputable section

theorem columnAction_mem_relations {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (s : Fin 2) {x : Coordinates n} (hx : x ∈ relations t) :
    columnAction t s x ∈ relations t := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨w, i⟩, rfl⟩ := hx
    exact Submodule.subset_span ⟨(s :: w, i), rfl⟩
  | zero => simpa only [map_zero] using (relations t).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (relations t).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (relations t).smul_mem c ih

def quotientColumn {n : ℕ} (t : Fin 2 → Fin n → Fin n) (s : Fin 2) :
    Module.End (ZMod 2) (NormQuotient t) :=
  (relations t).mapQ (relations t) (columnAction t s) (by
    intro x hx
    exact columnAction_mem_relations t s hx)

theorem quotientColumn_mk {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (s : Fin 2) (x : Coordinates n) :
    quotientColumn t s ((relations t).mkQ x) =
      (relations t).mkQ (columnAction t s x) := rfl

/-- A small family spanning the seed and stable under both table columns spans
the entire norm quotient, provided every coordinate is reachable from the seed. -/
theorem finrank_quotient_le_of_columns {n m : ℕ} (t : Fin 2 → Fin n → Fin n)
    (seed : Fin n) (b : Fin m → Fin n)
    (reach : ∀ i : Fin n, ∃ w : List (Fin 2),
      wordAction t w (Pi.single seed 1) = Pi.single i 1)
    (hseed : (relations t).mkQ (Pi.single seed 1) ∈
      Submodule.span (ZMod 2) (Set.range fun j => (relations t).mkQ (Pi.single (b j) 1)))
    (hcol : ∀ s j, (relations t).mkQ (Pi.single (t s (b j)) 1) ∈
      Submodule.span (ZMod 2) (Set.range fun j => (relations t).mkQ (Pi.single (b j) 1))) :
    Module.finrank (ZMod 2) (NormQuotient t) ≤ m := by
  classical
  let S := Submodule.span (ZMod 2) (Set.range fun j => (relations t).mkQ (Pi.single (b j) 1))
  have hs (s : Fin 2) (x : NormQuotient t) (hx : x ∈ S) : quotientColumn t s x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [quotientColumn_mk, columnAction_single]
      exact hcol s j
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using S.add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using S.smul_mem c ih
  have hw (w : List (Fin 2)) :
      (relations t).mkQ (wordAction t w (Pi.single seed 1)) ∈ S := by
    induction w with
    | nil => exact hseed
    | cons s w ih =>
      change (relations t).mkQ (columnAction t s (wordAction t w (Pi.single seed 1))) ∈ S
      rw [← quotientColumn_mk]
      exact hs s _ ih
  have hi (i : Fin n) : (relations t).mkQ (Pi.single i 1) ∈ S := by
    obtain ⟨w, hw'⟩ := reach i
    rw [← hw']
    exact hw w
  have htop : S = ⊤ := by
    apply top_unique
    intro u _
    obtain ⟨x, rfl⟩ := (relations t).mkQ_surjective u
    rw [pi_eq_sum_univ' x, map_sum]
    exact S.sum_mem (fun i _ => by simpa only [map_smul] using S.smul_mem (x i) (hi i))
  simpa only [Fintype.card_fin] using finrank_le_of_span_eq_top htop

/-- A direct consumer of the small-column criterion in the original HS module. -/
def of_quotient_columns {n m : ℕ} (t : Fin 2 → Fin n → Fin n)
    (seed : Fin n) (b : Fin m → Fin n) (hm : m < 40)
    (reach : ∀ i : Fin n, ∃ w : List (Fin 2),
      wordAction t w (Pi.single seed 1) = Pi.single i 1)
    (hseed : (relations t).mkQ (Pi.single seed 1) ∈
      Submodule.span (ZMod 2) (Set.range fun j => (relations t).mkQ (Pi.single (b j) 1)))
    (hcol : ∀ s j, (relations t).mkQ (Pi.single (t s (b j)) 1) ∈
      Submodule.span (ZMod 2) (Set.range fun j => (relations t).mkQ (Pi.single (b j) 1)))
    (v : Fin n → CosetNormModule) (hv : v seed = cosetNormVector 1)
    (hact : ∀ s i, cosetNormRepresentation (generator s) (v i) = v (t s i))
    (r : ℕ)
    (hr : ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, cosetNormRepresentation.asAlgebraHom x = 0) →
        xs.prod ∈ fiveNormIdeal) : NormCertificate :=
  of_quotient_bound t v seed hv hact
    (lt_of_le_of_lt (finrank_quotient_le_of_columns t seed b reach hseed hcol) hm) r hr

end
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
