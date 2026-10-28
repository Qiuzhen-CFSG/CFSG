/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.DodecadParameters
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeLocalSimple

/-!
# DodecadParameterCount

Dodecads containing a specified tetrad are parametrized by a nonzero hexacode word
vanishing there and an admissible binary mask. Counting the mask fibers gives 120
parameters; injectivity of the encoder identifies them with the actual dodecads.

Source: `Atlas/Codes/DodecadParameterCount.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

abbrev DodecadParameters (i : HexIndex) :=
  Σ h : {h : hexZeroCoordinate i // h ≠ 0},
    {r : P6 // r.val (hexIndexEquiv i) = 1 ∧
      ∀ j, j ≠ i → h.val.val.val j = 0 → r.val (hexIndexEquiv j) = 0}

abbrev DodecadsThroughTetrad (i : HexIndex) :=
  {D : Dodecad // tetrad i ⊆ D.val}

theorem dodecad_mask_fiber_card (i j : HexIndex) (hji : j ≠ i) :
    Nat.card {r : P6 // r.val (hexIndexEquiv i) = 1 ∧ r.val (hexIndexEquiv j) = 0} = 8 := by
  classical
  let e : Fin 2 ↪ Fin 6 := ⟨![hexIndexEquiv i,hexIndexEquiv j], by
    intro x y he
    fin_cases x <;> fin_cases y <;> simp_all⟩
  have he (r : P6) : parityProjection e r = ![1,0] ↔
      r.val (hexIndexEquiv i) = 1 ∧ r.val (hexIndexEquiv j) = 0 := by
    constructor
    · intro h
      exact ⟨congrFun h 0,congrFun h 1⟩
    · rintro ⟨h0,h1⟩
      funext k
      fin_cases k
      · exact h0
      · exact h1
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, he] using
    (parityProjection_fiber e ![1,0])

theorem dodecad_parameter_fiber_card (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    Nat.card {r : P6 // r.val (hexIndexEquiv i) = 1 ∧
      ∀ j, j ≠ i → h.val.val j = 0 → r.val (hexIndexEquiv j) = 0} = 8 := by
  obtain ⟨j, hj, huniq⟩ := hexZeroCoordinate_unique_other_zero i h hh
  have he (r : P6) :
      (r.val (hexIndexEquiv i) = 1 ∧
        ∀ j, j ≠ i → h.val.val j = 0 → r.val (hexIndexEquiv j) = 0) ↔
      (r.val (hexIndexEquiv i) = 1 ∧ r.val (hexIndexEquiv j) = 0) := by
    constructor
    · rintro ⟨hi,hr⟩
      exact ⟨hi,hr j hj.1 hj.2⟩
    · rintro ⟨hi,hr⟩
      refine ⟨hi,fun k hki hk => ?_⟩
      rw [huniq k ⟨hki,hk⟩]
      exact hr
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact dodecad_mask_fiber_card i j hj.1

theorem dodecadParameters_card (i : HexIndex) : Nat.card (DodecadParameters i) = 120 := by
  classical
  have hf (h : {h : hexZeroCoordinate i // h ≠ 0}) :
      Fintype.card {r : P6 // r.val (hexIndexEquiv i) = 1 ∧
        ∀ j, j ≠ i → h.val.val.val j = 0 → r.val (hexIndexEquiv j) = 0} = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact dodecad_parameter_fiber_card i h.val h.prop
  simp only [DodecadParameters, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hexZeroCoordinate_nonzero_card]

def dodecadParametersSupport (i : HexIndex) (p : DodecadParameters i) : DodecadsThroughTetrad i :=
  ⟨⟨support (c0Encoder (p.1.val.val,p.2.val)), by
    obtain ⟨j,hj,_⟩ := hexZeroCoordinate_unique_other_zero i p.1.val p.1.prop
    exact (dodecad_parameters_converse i p.1.val p.1.prop p.2.val p.2.prop.1
      j hj.1 hj.2 (p.2.prop.2 j hj.1 hj.2)).1⟩,
    (c0Encoder_contains_tetrad _ _ i).mpr ⟨p.1.val.prop,p.2.prop.1⟩⟩

theorem dodecadParametersSupport_bijective (i : HexIndex) :
    Function.Bijective (dodecadParametersSupport i) := by
  constructor
  · rintro ⟨h,r⟩ ⟨h',r'⟩ he
    have hs : support (c0Encoder (h.val.val,r.val)) =
        support (c0Encoder (h'.val.val,r'.val)) :=
      congrArg (fun D : DodecadsThroughTetrad i => D.val.val) he
    obtain ⟨hh,hr⟩ := dodecad_parameters_unique _ _ _ _ hs
    have hh' : h = h' := Subtype.ext (Subtype.ext hh)
    subst h'
    have hr' : r = r' := Subtype.ext hr
    subst r'
    rfl
  · intro D
    obtain ⟨w,hw,hs⟩ := (dodecads_mem D.val.val).mp D.val.prop
    obtain ⟨h,r,hh,he,ri,j,hj,huniq⟩ :=
      dodecad_parameters_exist w hw i (hs.symm ▸ D.prop)
    have hr : ∀ k, k ≠ i → h.val.val k = 0 → r.val (hexIndexEquiv k) = 0 := by
      intro k hki hk
      exact dodecad_parameters_empty h.val r i k (he.symm ▸ hw) h.prop ri hki hk
    refine ⟨⟨⟨h,hh⟩,⟨r,ri,hr⟩⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change support (c0Encoder (h.val,r)) = D.val.val
    rw [he,hs]

def dodecadParametersEquiv (i : HexIndex) : DodecadParameters i ≃ DodecadsThroughTetrad i :=
  Equiv.ofBijective _ (dodecadParametersSupport_bijective i)

theorem dodecadsThroughTetrad_card (i : HexIndex) : Nat.card (DodecadsThroughTetrad i) = 120 := by
  rw [← Nat.card_congr (dodecadParametersEquiv i), dodecadParameters_card]

end Atlas.Codes
