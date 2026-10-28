module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveGeometry
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleCensus

/-!
# Exact full-extension order for PSU₅(4) completions

The odd-distance shells in the proved quadrangle contain 65 + 65·16·64
plane vertices. Identical marked endpoint orders give equality with the
full extension order, retaining its entire outer degree and the native
projective scalar quotient. This proves the order clause of
Aschbacher–Smith F.4.13,24 (`refs/quasithin.pdf`, pp.280,287).
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.PathTransitivePolygon

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
count in an arbitrary small unitary-five extension completion. -/
theorem five_completion_card_planes (U : GreenBook.UnitaryFive.Model 4)
    (E : FiveExtension U) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card (M ⧸ c.cosetFamily true) = fiveCosetCount true := by
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  obtain ⟨hg,hd,_⟩ := five_completion_quadrangle U E c hoverlap horder
  have hc := five_completion_card_neighbors U E c hoverlap
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> simp [fiveDegree])
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
    (fun v : Vertex c.cosetFamily => v.type) fiveDegree hf hc
  have h1 := hpaths 0 (base c.cosetFamily false)
  have h3 := hpaths 2 (base c.cosetFamily false)
  change Nat.card {p : BasedWalk (graph c.cosetFamily) 1 (base c.cosetFamily false) // p.Nonbacktracking} = _ at h1
  change Nat.card {p : BasedWalk (graph c.cosetFamily) 3 (base c.cosetFamily false) // p.Nonbacktracking} = _ at h3
  rw [h1,h3] at h
  exact h.trans (by norm_num [fiveCosetCount,fiveDegree,BasedWalk.forwardCount])

/-- F.4.13(2) and the order clause of F.4.24: a faithful completion below
the full extension bound has exactly that full carrier order. -/
theorem five_completion_card_eq (U : GreenBook.UnitaryFive.Model 4)
    (E : FiveExtension U) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card M = Nat.card E.carrier := by
  have hl : Nat.card (c.cosetFamily true) = Nat.card (E.family true) :=
    c.right_card.trans (Nat.card_congr (subgroupOfEquivOfLe E.right_le).toEquiv).symm
  have hn : Nat.card (E.carrier ⧸ E.family true) = fiveCosetCount true :=
    (E.card_coset_eq_native (five_conj_injective U) true).trans (five_native_card_coset U true)
  calc
    Nat.card M = Nat.card (c.cosetFamily true) * Nat.card (M ⧸ c.cosetFamily true) :=
      (c.cosetFamily true).card_mul_index.symm
    _ = Nat.card (E.family true) * Nat.card (E.carrier ⧸ E.family true) := by
      rw [hl,five_completion_card_planes U E c hoverlap horder,hn]
    _ = Nat.card E.carrier := (E.family true).card_mul_index
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
