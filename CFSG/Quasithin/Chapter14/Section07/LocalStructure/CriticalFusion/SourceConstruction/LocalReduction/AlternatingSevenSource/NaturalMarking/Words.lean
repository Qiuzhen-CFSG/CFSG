module
public import Theory.Representation.BinaryPermutation.SevenSourceCubics.Alternating
public import Theory.Representation.BinaryPermutation.SevenSourceSpan
public import Theory.Representation.BinaryPermutation.SevenParabolic.Geometry

/-!
# The source Sylow's fixed words in the seven-letter natural module

The alternating Sylow has three coordinate orbits, of sizes two, four and
one. Its fixed even words are zero, the pair, the four, and their sum. A
binary plane whose nonzero words have constant weight cannot contain a
weight-six word, since the sum of two such words has weight zero or two.
Source: Aschbacher–Smith, 14.7.50, printed pp.1064–1065, refs/quasithin.pdf.
-/

@[expose] public section
open Equiv Module
open BinaryPermutation
open BinaryPermutation.SevenParabolic
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking

/-- Every vector fixed by the alternating source Sylow is one of four words. -/
theorem fixed_word_cases (v : Space)
    (hfixed : ∀ g ∈ SevenSourceCubics.Alternating.two,
      alternatingCoreRepresentation (Fin 7) g v = v) :
    v = 0 ∨ v = SevenSourceSpan.point ∨ v = SevenSourceCubics.point ∨
      v = SevenSourceSpan.point + SevenSourceCubics.point := by
  let a : alternatingGroup (Fin 7) :=
    ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩
  let b : alternatingGroup (Fin 7) :=
    ⟨swap 0 1 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩
  let c : alternatingGroup (Fin 7) :=
    ⟨swap 2 4 * swap 3 5, by rw [Perm.mem_alternatingGroup]; decide⟩
  have ha := hfixed a (by decide)
  have hb := hfixed b (by decide)
  have hc := hfixed c (by decide)
  have h01 : v.val 0 = v.val 1 :=
    (congrArg (fun w : Space => w.val 0) ha).symm
  have h23 : v.val 2 = v.val 3 :=
    (congrArg (fun w : Space => w.val 2) ha).symm
  have h45 : v.val 4 = v.val 5 :=
    (congrArg (fun w : Space => w.val 4) hb).symm
  have h24 : v.val 2 = v.val 4 :=
    (congrArg (fun w : Space => w.val 2) hc).symm
  have words : ∀ w : Full (Fin 7), (∑ i, w i) = 0 →
      w 0 = w 1 → w 2 = w 3 → w 4 = w 5 → w 2 = w 4 →
      w = 0 ∨ w = ![1,1,0,0,0,0,0] ∨ w = ![0,0,1,1,1,1,0] ∨
        w = ![1,1,0,0,0,0,0] + ![0,0,1,1,1,1,0] := by decide +kernel
  simpa only [Subtype.ext_iff, Submodule.coe_zero, Submodule.coe_add,
    SevenSourceSpan.point, SevenSourceCubics.point] using
    words v.val v.property h01 h23 h45 h24

/-- The same fixed-word classification applies to the full symmetric Sylow. -/
theorem symmetric_fixed_word_cases (v : Space)
    (hfixed : ∀ g ∈ standardTwo, coreRepresentation (Fin 7) g v = v) :
    v = 0 ∨ v = SevenSourceSpan.point ∨ v = SevenSourceCubics.point ∨
      v = SevenSourceSpan.point + SevenSourceCubics.point :=
  fixed_word_cases v (fun g hg => hfixed g.val hg)

private def sixWord (i : Fin 7) : Full (Fin 7) := fun j => if j = i then 0 else 1

private theorem weight_six_word (v : Space) (hv : weight v = 6) :
    ∃ i : Fin 7, v.val = sixWord i := by
  have words : ∀ w : Full (Fin 7),
      (Finset.univ.filter (fun i => w i ≠ 0)).card = 6 →
        ∃ i : Fin 7, w = sixWord i := by decide +kernel
  exact words v.val hv

/-- Two weight-six words never sum to another weight-six word. -/
theorem weight_six_add_ne_six (v w : Space)
    (hv : weight v = 6) (hw : weight w = 6) : weight (v + w) ≠ 6 := by
  obtain ⟨i, hi⟩ := weight_six_word v hv
  obtain ⟨j, hj⟩ := weight_six_word w hw
  have pairs : ∀ i j : Fin 7,
      (Finset.univ.filter (fun k => (sixWord i + sixWord j) k ≠ 0)).card ≠ 6 :=
    by decide +kernel
  simpa only [weight, Submodule.coe_add, hi, hj] using pairs i j

/-- A constant-weight binary subspace of dimension at least two has no weight-six word. -/
theorem plane_weight_ne_six (U : Submodule (ZMod 2) Space)
    (hd : 1 < finrank (ZMod 2) U) (v : Space) (hv : v ∈ U)
    (hweight : ∀ x ∈ U, x ≠ 0 → weight x = weight v) : weight v ≠ 6 := by
  intro hsix
  have hdim : finrank (ZMod 2) U ≤ 1 := by
    apply finrank_le_one (⟨v,hv⟩ : U)
    intro x
    by_cases hx : (x : Space) = 0
    · exact ⟨0, by simpa using (Subtype.ext hx).symm⟩
    have he : (x : Space) = v := by
      by_contra hne
      have hsum : (x : Space) + v ≠ 0 := by
        intro he
        apply hne
        have hh := congrArg (fun y : Space => y + v) he
        simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh
      apply weight_six_add_ne_six x v ((hweight x x.property hx).trans hsix) hsix
      exact (hweight (x + v) (U.add_mem x.property hv) hsum).trans hsix
    exact ⟨1, by simpa using (Subtype.ext he).symm⟩
  omega

/-- A nonzero fixed word in a constant-weight plane is the pair or the four. -/
theorem fixed_word_pair_or_four_of_plane (U : Submodule (ZMod 2) Space)
    (hd : finrank (ZMod 2) U = 2) (v : Space) (hv : v ∈ U) (hvn : v ≠ 0)
    (hweight : ∀ x ∈ U, x ≠ 0 → weight x = weight v)
    (hfixed : ∀ g ∈ SevenSourceCubics.Alternating.two,
      alternatingCoreRepresentation (Fin 7) g v = v) :
    v = SevenSourceSpan.point ∨ v = SevenSourceCubics.point := by
  rcases fixed_word_cases v hfixed with h | h | h | h
  · exact (hvn h).elim
  · exact Or.inl h
  · exact Or.inr h
  · have hn := plane_weight_ne_six U (by omega) v hv hweight
    exact (hn (h ▸ (by decide))).elim

/-- The constant-weight conclusion for the symmetric source Sylow. -/
theorem symmetric_fixed_word_pair_or_four_of_plane (U : Submodule (ZMod 2) Space)
    (hd : finrank (ZMod 2) U = 2) (v : Space) (hv : v ∈ U) (hvn : v ≠ 0)
    (hweight : ∀ x ∈ U, x ≠ 0 → weight x = weight v)
    (hfixed : ∀ g ∈ standardTwo, coreRepresentation (Fin 7) g v = v) :
    v = SevenSourceSpan.point ∨ v = SevenSourceCubics.point :=
  fixed_word_pair_or_four_of_plane U hd v hv hvn hweight (fun g hg => hfixed g.val hg)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking
