/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernarySupportedHexad.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.TernaryGolaySupports

/-!
# TernarySupportedHexad

The code shortened to a hexad is its scalar line; hexad multipliers must therefore be constant.
Minimum distance also shows that a constant hexad and one outside value determine a constant word.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernarySupportedHexad.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


namespace Atlas.Codes

/-- The code shortened to any actual weight-six support is exactly its one-dimensional line. -/
theorem ternaryGolay_supported_hexad (c : TernarySixWords) (w : ternaryGolay)
    (hw : ternarySupport w.val ⊆ ternarySupport c.val.val) :
    ∃ a : ZMod 3,w.val=a • c.val.val := by
  by_cases hz : w.val=0
  · exact ⟨0,by simp [hz]⟩
  have hmin := ternaryGolay_minimum w.val w.property hz
  have hle : ternaryWeight w.val ≤ 6 := by
    have h := Finset.card_le_card hw
    simpa only [ternarySupport_card,c.property] using h
  have hweight : ternaryWeight w.val=6 := by omega
  have hinter : 5 ≤ (ternarySupport c.val.val ∩ ternarySupport w.val).card := by
    rw [Finset.inter_eq_right.mpr hw,ternarySupport_card,hweight]
    decide
  rcases ternaryGolay_hexad_intersection c.val.val w.val c.val.property w.property
    c.property hweight hinter with he|he
  · exact ⟨1,by simpa using he⟩
  · exact ⟨-1,by simpa using he⟩

/-- Multiplying a weight-six word coordinatewise by a word stays in the code
only if the multiplier is constant on that support. -/
theorem ternaryGolay_hexad_multiplier_constant (c : TernarySixWords) (t : TernaryWord)
    (ht : (fun i => c.val.val i*t i) ∈ ternaryGolay) :
    ∃ a : ZMod 3,∀ i ∈ ternarySupport c.val.val,t i=a := by
  obtain ⟨a,ha⟩ := ternaryGolay_supported_hexad c ⟨_,ht⟩ (by
    intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,fun he => hh (by simp [he])⟩)
  refine ⟨a,?_⟩
  intro i hi
  have hn : c.val.val i≠0 := (Finset.mem_filter.mp hi).2
  have he := congrFun ha i
  change c.val.val i*t i=a*c.val.val i at he
  exact mul_left_cancel₀ hn (by simpa only [mul_comm a] using he)

/-- A codeword constant on a hexad and one further coordinate is globally constant. -/
theorem ternaryGolay_constant_hexad_point (c : TernarySixWords) (w : ternaryGolay)
    (a : ZMod 3) (hS : ∀ i ∈ ternarySupport c.val.val,w.val i=a)
    (j : Fin 12) (hj : j ∉ ternarySupport c.val.val) (hwj : w.val j=a) :
    ∀ i,w.val i=a := by
  let v : ternaryGolay := w-a • ⟨1,ternaryGolay_one⟩
  have hs : ternarySupport v.val ⊆ (ternarySupport c.val.val)ᶜ.erase j := by
    intro i hi
    have hn : v.val i≠0 := (Finset.mem_filter.mp hi).2
    have hij : i≠j := by intro he; subst i; exact hn (by change w.val j-a*1=0; rw [hwj]; ring)
    have his : i ∉ ternarySupport c.val.val := by
      intro his
      exact hn (by change w.val i-a*1=0; rw [hS i his]; ring)
    exact Finset.mem_erase.mpr ⟨hij,Finset.mem_compl.mpr his⟩
  have hcard : ((ternarySupport c.val.val)ᶜ.erase j).card=5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_compl.mpr hj),Finset.card_compl,
      Fintype.card_fin,ternarySupport_card,c.property]
  have hv : v.val=0 := by
    by_contra h
    have hmin := ternaryGolay_minimum v.val v.property h
    have hle := Finset.card_le_card hs
    rw [hcard,ternarySupport_card] at hle
    omega
  intro i
  have he := congrFun hv i
  change w.val i-a*1=0 at he
  simpa using sub_eq_zero.mp he

end Atlas.Codes
