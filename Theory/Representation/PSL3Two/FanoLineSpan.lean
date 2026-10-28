module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Fano
public import Theory.Representation.BinaryPermutation
public import Mathlib.LinearAlgebra.Dimension.RankNullity
/-!
# Binary Fano line spans

The seven three-point line vectors span a four-dimensional subspace of the
affine evaluation space; four explicit line vectors give a basis. The three lines through a point are independent. Consequently every
linear image killing that pencil sends the full line span to a space of dimension
at most one. The small pencil calculation is checked by kernel reduction.

This is the local H.5.3 calculation used in Aschbacher–Smith, I.5.10,
combined manuscript of 1 March 2004, printed p.422.
-/

@[expose] public section

open Module
namespace BinaryLinearThree.FanoLineSpan
open Matrix.PSL3Two.Fano
abbrev Full := Point → ZMod 2
def lineVector (l : Line) : Full := fun p => if Incident p l then 1 else 0
def lineSpan : Submodule (ZMod 2) Full := Submodule.span _ (Set.range lineVector)
def pencil (p : Point) : Submodule (ZMod 2) Full :=
  Submodule.span _ (Set.range fun l : {l : Line // Incident p l} => lineVector l.val)
def affineEvaluation : (ZMod 2 × Vector) →ₗ[ZMod 2] Full where
  toFun a p := a.1 + dotProduct p.val a.2
  map_add' a b := by ext p; simp [dotProduct_add]; ring
  map_smul' c a := by ext p; simp [dotProduct_smul]; ring
private theorem line_mem_range (l : Line) : lineVector l ∈ LinearMap.range affineEvaluation := by
  refine ⟨(1, l.normal.val), ?_⟩
  ext p
  change 1 + dotProduct p.val l.normal.val = if Incident p l then 1 else 0
  split_ifs with h
  · change dotProduct p.val l.normal.val = 0 at h
    rw [h, add_zero]
  · have h' : dotProduct p.val l.normal.val ≠ 0 := h
    have he := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ h'
    rw [he]
    rfl
theorem finrank_lineSpan_le : finrank (ZMod 2) lineSpan ≤ 4 := by
  have h : lineSpan ≤ LinearMap.range affineEvaluation :=
    Submodule.span_le.mpr (by rintro v ⟨l, rfl⟩; exact line_mem_range l)
  calc
    finrank (ZMod 2) lineSpan ≤ finrank (ZMod 2) (LinearMap.range affineEvaluation) :=
      Submodule.finrank_mono h
    _ ≤ finrank (ZMod 2) (ZMod 2 × Vector) := LinearMap.finrank_range_le _
    _ = 4 := by simp [Matrix.PSL3Two.Fano.Vector]
set_option maxRecDepth 10000 in
private theorem pencil_coefficients : ∀ p : Point,
    ∀ c : {l : Line // Incident p l} → ZMod 2,
      (∑ l, c l • lineVector l.val) = 0 → c = 0 := by
  decide +kernel
theorem pencil_independent (p : Point) :
    LinearIndependent (ZMod 2) (fun l : {l : Line // Incident p l} => lineVector l.val) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc l
  exact congrFun (pencil_coefficients p c hc) l
theorem finrank_pencil (p : Point) : finrank (ZMod 2) (pencil p) = 3 := by
  rw [pencil, finrank_span_eq_card (pencil_independent p), lines_through_point]
theorem pencil_le (p : Point) : pencil p ≤ lineSpan := by
  apply Submodule.span_le.mpr
  rintro v ⟨l, rfl⟩
  exact Submodule.subset_span ⟨l.val, rfl⟩
theorem finrank_map_le_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : Point) (f : Full →ₗ[ZMod 2] V)
    (hf : ∀ l, Incident p l → f (lineVector l) = 0) :
    finrank (ZMod 2) (lineSpan.map f) ≤ 1 := by
  have hp : pencil p ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro v ⟨l, rfl⟩
    exact hf l.val l.property
  have hk : (pencil p).comap lineSpan.subtype ≤ (f.domRestrict lineSpan).ker := by
    intro v hv
    exact hp hv
  have hd : finrank (ZMod 2) ((pencil p).comap lineSpan.subtype) = 3 := by
    rw [(Submodule.comapSubtypeEquivOfLe (pencil_le p)).finrank_eq, finrank_pencil]
  have hm := Submodule.finrank_mono hk
  have hr := (f.domRestrict lineSpan).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict] at hr
  have hb := finrank_lineSpan_le
  omega
private def frame : Fin 4 → Line :=
  ![⟨⟨![1,0,0], by decide⟩⟩, ⟨⟨![0,1,0], by decide⟩⟩,
    ⟨⟨![0,0,1], by decide⟩⟩, ⟨⟨![1,1,0], by decide⟩⟩]
private theorem frame_independent : LinearIndependent (ZMod 2) (lineVector ∘ frame) := by
  rw [Fintype.linearIndependent_iff]
  decide +kernel
theorem finrank_lineSpan : finrank (ZMod 2) lineSpan = 4 := by
  apply le_antisymm finrank_lineSpan_le
  have he : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (lineVector ∘ frame))) = 4 := by
    rw [finrank_span_eq_card frame_independent, Fintype.card_fin]
  rw [← he]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  exact Submodule.subset_span ⟨frame i, rfl⟩
end BinaryLinearThree.FanoLineSpan
