module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Residue
/-!
# Native octad overlap and exclusion of the far orbital

A matching of the six tetrads has an edge disjoint from any prescribed
pair. Thus every trio of a sextet contains an octad disjoint from a given
octad of that sextet. Its Golay codeword belongs to the prescribed octad
radical and hence to the radical sum of any line containing that octad.
This proves the native exclusion of δ₄ used in AS91 (7.4).

Source: Aschbacher–Segev (1991), (3.13.1), p.596.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Theory.SpecificGroups.SymmetricSix

/-- An octad of the native sextet, as the union of two actual tetrads. -/
def PlaneOctad (π : Plane) (A : Finset (Fin 24)) : Prop :=
  ∃ B ∈ π.parts, ∃ C ∈ π.parts, B ≠ C ∧ A = B ∪ C

theorem planeOctad_duad (π : Plane) (e : Fin 6 ≃ {A // A ∈ π.parts})
    {A : Finset (Fin 24)} (hA : PlaneOctad π A) :
    ∃ a : Duad, duadOctad π e a = A := by
  obtain ⟨B,hB,C,hC,hBC,rfl⟩ := hA
  obtain ⟨i,hi⟩ := e.surjective ⟨B,hB⟩
  obtain ⟨j,hj⟩ := e.surjective ⟨C,hC⟩
  have hij : i ≠ j := by rintro rfl; exact hBC (congrArg Subtype.val (hi.symm.trans hj))
  have complete : ∀ i j : Fin 6, i ≠ j → ∃ a : Duad, duadSet a = {i,j} := by decide
  obtain ⟨a,ha⟩ := complete i j hij
  refine ⟨a, ?_⟩
  simp [duadOctad,tetradUnion,ha,hi,hj]

theorem disjoint_octad_word_mem_radical {A B : Finset (Fin 24)}
    (hB : B ∈ m24Blocks) (hd : Disjoint A B) :
    ∃ v : MathieuCode.golay, v ∈ radical A ∧ v.val = MathieuCode.wordOfSet B := by
  have hw : MathieuCode.wordOfSet B ∈ MathieuCode.golay := by
    rw [MathieuCode.golay_eq_span_octads]
    exact Submodule.subset_span ⟨B,hB,rfl⟩
  refine ⟨⟨MathieuCode.wordOfSet B,hw⟩, ?_, rfl⟩
  intro w
  apply Finset.sum_eq_zero
  intro i hi
  have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
  simp [MathieuCode.wordOfSet,hn]

theorem octad_in_radicalSum_of_disjoint {l : Line} {A B : Finset (Fin 24)}
    (hA : A ∈ l.parts) (hB : B ∈ m24Blocks) (hd : Disjoint A B) :
    ∃ v : MathieuCode.golay, v ∈ radicalSum l ∧ v.val = MathieuCode.wordOfSet B := by
  obtain ⟨v,hv,he⟩ := disjoint_octad_word_mem_radical hB hd
  exact ⟨v,(le_iSup (fun A : {A // A ∈ l.parts} => radical A.val) ⟨A,hA⟩) hv,he⟩

private theorem syntheme_disjoint_duad (a : Duad) (s : Syntheme) :
    ∃ b, incident b s ∧ Disjoint (duadSet a) (duadSet b) := by decide +revert

/-- Any trio incident to a sextet has an octad disjoint from a prescribed
 octad of that sextet. -/
theorem incident_has_disjoint_octad {π : Plane} {m : Line} {A : Finset (Fin 24)}
    (hm : Incident m π) (hA : PlaneOctad π A) :
    ∃ B ∈ m.parts, Disjoint A B := by
  classical
  let e : Fin 6 ≃ {A // A ∈ π.parts} :=
    (Fintype.equivFinOfCardEq (by simpa using π.card)).symm
  obtain ⟨a,rfl⟩ := planeOctad_duad π e hA
  obtain ⟨b,hb,hd⟩ := syntheme_disjoint_duad a (residueEquiv π e ⟨m,hm⟩)
  exact ⟨duadOctad π e b,(residueEquiv_incidence π e ⟨m,hm⟩ b).mp hb,
    tetradUnion_disjoint π e hd⟩

/-- AS91 (3.13.1): a line sharing an octad with a sextet is never δ₄
 from an incident line of that sextet. -/
theorem not_delta_four_of_plane_octad {l m : Line} {π : Plane}
    (hl : ∃ A ∈ l.parts, PlaneOctad π A) (hm : Incident m π) : ¬ Delta 4 l m := by
  obtain ⟨A,hA,hAπ⟩ := hl
  obtain ⟨B,hBm,hd⟩ := incident_has_disjoint_octad hm hAπ
  obtain ⟨v,hv,he⟩ := octad_in_radicalSum_of_disjoint hA (m.octad B hBm) hd
  intro hdelta
  have hB : B ∈ octadsInRadicalSum l m := ⟨hBm,v,hv,he⟩
  change octadsInRadicalSum l m = ∅ at hdelta
  rw [hdelta] at hB
  exact hB

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
