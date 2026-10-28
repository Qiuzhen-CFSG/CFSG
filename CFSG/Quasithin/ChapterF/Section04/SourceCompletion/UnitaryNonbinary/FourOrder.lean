module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourGeometry
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleCensus

/-!
# Exact order of a small full unitary-four extension completion

The proved quadrangle has unique paths of length one or three to every
plane vertex from a point. The two unequal branching factors give exactly
(q³ + 1)(q + 1) plane cosets. The identical marked endpoint orders then
give equality of the completion order with the full extension carrier.
No restriction on the outer degree or group-identification premise is used.

Source: Aschbacher–Smith F.4.13(2) and F.4.24, pp.280 and287.
Hermitian identification, the remaining conclusion of F.4.24, is separate.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.PathTransitivePolygon
open GreenBook.LieModels.UnitaryFour Theory.SpecificGroups.ClassicalUnitary

private def planeFiberEquiv {M : Type*} [Group M] (P : Bool → Subgroup M) :
    {v : Vertex P // v.type ≠ false} ≃ M ⧸ P true where
  toFun v := by
    rcases v with ⟨⟨i,q⟩,hi⟩
    cases i
    · exact (hi rfl).elim
    · exact q
  invFun q := ⟨⟨true,q⟩, Bool.false_ne_true.symm⟩
  left_inv v := by
    rcases v with ⟨⟨i,q⟩,hi⟩
    cases i
    · exact (hi rfl).elim
    · rfl
  right_inv q := rfl

/-- Counting the two odd-distance shells gives the exact native plane-coset
count in an arbitrary small unitary-four extension completion. -/
theorem four_completion_card_planes (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
    (E : FourExtension m hm) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card (M ⧸ c.cosetFamily true) = fourCosetCount m true := by
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  obtain ⟨hg,hd,_⟩ := four_completion_quadrangle m hm hmgt E c hoverlap horder
  have hc := four_completion_card_neighbors m hm E c hoverlap
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> simp [fourDegree])
  have hf : ∀ {v w : Vertex c.cosetFamily}, (graph c.cosetFamily).Adj v w → w.type = !v.type := by
    intro v w h
    have hh := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have h := QuadrangleRecognition.card_opposite_of_quadrangle
    (Subgroup.CosetGeometry.RankTwo.connected c.cosetFamily c.generated)
    (fun v : Vertex c.cosetFamily => v.type) (fun h => h.1) hg hd (base c.cosetFamily false)
  change Nat.card {v : Vertex c.cosetFamily // v.type ≠ false} = _ at h
  rw [Nat.card_congr (planeFiberEquiv c.cosetFamily)] at h
  have hpaths := BasedWalk.card_nonbacktracking_succ (graph c.cosetFamily)
    (fun v : Vertex c.cosetFamily => v.type) (fourDegree m) hf hc
  have h1 := hpaths 0 (base c.cosetFamily false)
  have h3 := hpaths 2 (base c.cosetFamily false)
  change Nat.card {p : BasedWalk (graph c.cosetFamily) 1 (base c.cosetFamily false) // p.Nonbacktracking} = _ at h1
  change Nat.card {p : BasedWalk (graph c.cosetFamily) 3 (base c.cosetFamily false) // p.Nonbacktracking} = _ at h3
  rw [h1,h3] at h
  exact h.trans (by simp [fourCosetCount,fourDegree,BasedWalk.forwardCount]; ring)

/-- F.4.13(2) and the order clause of F.4.24: a faithful completion below
the full extension bound has exactly that full carrier order. -/
theorem four_completion_card_eq (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
    (E : FourExtension m hm) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card M = Nat.card E.carrier := by
  let : Finite (ProjectiveGroup m hm) := Finite.of_surjective (projection m hm)
    (UnitaryFourFlag.project_surjective _ _)
  have hl : Nat.card (c.cosetFamily true) = Nat.card (E.family true) := by
    rw [← E.completion_family (parabolics_generate m hm)]
    exact c.right_card.trans (E.completion (parabolics_generate m hm)).right_card.symm
  have hn : Nat.card (E.carrier ⧸ E.family true) = fourCosetCount m true :=
    (E.card_coset_eq_native (four_conj_injective m hm) true).trans (four_native_card_coset m hm true)
  calc
    Nat.card M = Nat.card (c.cosetFamily true) * Nat.card (M ⧸ c.cosetFamily true) :=
      (c.cosetFamily true).card_mul_index.symm
    _ = Nat.card (E.family true) * Nat.card (E.carrier ⧸ E.family true) := by
      rw [hl,four_completion_card_planes m hm hmgt E c hoverlap horder,hn]
    _ = Nat.card E.carrier := (E.family true).card_mul_index
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
