module

public import Mathlib.FieldTheory.Finiteness
public import Theory.Representation.BinaryPermutation
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-!
# The canonical natural-module flag

The natural module is the even-weight binary permutation module modulo the
constant vector.  The pair vectors below are the classes of characteristic
vectors of duads.  The point line is the span of `v₄₅`; the plane is the span
of `v₀₁` and `v₂₃`. Their stabilizers are exactly the duad and syntheme
stabilizers `H1` and `H2`; restriction to the alternating group gives `L1`
and `L2`.

For uniqueness, the fifteen duads parametrize the nonzero vectors of the
actual natural module. Subtracting the last coordinate detects distinct duad
classes; cardinality then proves exhaustiveness. Kernel-checked finite
certificates compute the duad orbits of eight words in `(01)(45)`, `(23)(45)`,
and `(02)(13)`. Only `{4,5}` has orbit of size at most one, and only the three
canonical duads have orbit of size at most three. An invariant subspace
contains these orbits and zero, giving uniqueness in dimensions one and two.
No identification with a separate symplectic representation is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.3, printed pp.83–85, and Notation 13.2.1,
printed p.877. This module supplies the natural-module flag geometry only;
the residual and intersection conventions are kept distinct in `BinaryFlags`.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

open Module
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

abbrev Ω := Fin 6
abbrev V := natural Ω

/-- For distinct indices, the class of the characteristic vector of `{i,j}`. -/
def pairVector (i j : Ω) : V :=
  ⟨(constants Ω).mkQ (Pi.single i (1 : ZMod 2) + Pi.single j 1),
    ⟨Pi.single i (1 : ZMod 2) + Pi.single j 1,
      by simp [mem_core]; decide +revert,
      rfl⟩⟩

def canonicalLine : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {pairVector 4 5}

def canonicalPlane : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {pairVector 0 1, pairVector 2 3}

theorem pairVector45_ne_zero : pairVector 4 5 ≠ 0 := by
  intro hz
  have hz' := congrArg Subtype.val hz
  change (constants Ω).mkQ (Pi.single (4 : Ω) (1 : ZMod 2) + Pi.single 5 1) = 0 at hz'
  have hc : Pi.single (4 : Ω) (1 : ZMod 2) + Pi.single 5 1 ∈ constants Ω :=
    (Submodule.Quotient.mk_eq_zero (constants Ω)).mp hz'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hc0 := congrFun hc (0 : Ω)
  have hc4 := congrFun hc (4 : Ω)
  simp [allOne] at hc0 hc4
  rw [hc4] at hc0
  exact one_ne_zero hc0

theorem pairVector01_ne_zero : pairVector 0 1 ≠ 0 := by
  intro hz
  have hz' := congrArg Subtype.val hz
  change (constants Ω).mkQ (Pi.single (0 : Ω) (1 : ZMod 2) + Pi.single 1 1) = 0 at hz'
  have hc : Pi.single (0 : Ω) (1 : ZMod 2) + Pi.single 1 1 ∈ constants Ω :=
    (Submodule.Quotient.mk_eq_zero (constants Ω)).mp hz'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hc0 := congrFun hc (0 : Ω)
  have hc2 := congrFun hc (2 : Ω)
  simp [allOne] at hc0 hc2
  rw [hc2] at hc0
  exact one_ne_zero hc0.symm

theorem pairVector23_ne_zero : pairVector 2 3 ≠ 0 := by
  intro hz
  have hz' := congrArg Subtype.val hz
  change (constants Ω).mkQ (Pi.single (2 : Ω) (1 : ZMod 2) + Pi.single 3 1) = 0 at hz'
  have hc : Pi.single (2 : Ω) (1 : ZMod 2) + Pi.single 3 1 ∈ constants Ω :=
    (Submodule.Quotient.mk_eq_zero (constants Ω)).mp hz'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hc0 := congrFun hc (0 : Ω)
  have hc2 := congrFun hc (2 : Ω)
  simp [allOne] at hc0 hc2
  rw [hc0] at hc2
  exact one_ne_zero hc2.symm

theorem pairVector01_ne_pairVector23 : pairVector 0 1 ≠ pairVector 2 3 := by
  intro h
  have hz : (constants Ω).mkQ
      ((Pi.single (0 : Ω) (1 : ZMod 2) + Pi.single 1 1) -
       (Pi.single 2 1 + Pi.single 3 1)) = 0 := by
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact congrArg Subtype.val h
  have hc : (Pi.single (0 : Ω) (1 : ZMod 2) + Pi.single 1 1) -
      (Pi.single 2 1 + Pi.single 3 1) ∈ constants Ω :=
    (Submodule.Quotient.mk_eq_zero (constants Ω)).mp hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hc1 := congrFun hc (1 : Ω)
  have hc4 := congrFun hc (4 : Ω)
  simp [allOne] at hc1 hc4
  rw [hc4] at hc1
  exact one_ne_zero hc1.symm

theorem canonicalLine_finrank : Module.finrank (ZMod 2) canonicalLine = 1 := by
  rw [canonicalLine, finrank_span_singleton pairVector45_ne_zero]

theorem canonicalPlane_finrank : Module.finrank (ZMod 2) canonicalPlane = 2 := by
  let b : Fin 2 → V := fun i => if i = 0 then pairVector 0 1 else pairVector 2 3
  have hb : LinearIndependent (ZMod 2) b := by
    rw [linearIndependent_fin2]
    constructor
    · exact pairVector23_ne_zero
    · intro a ha
      fin_cases a
      · apply pairVector01_ne_zero
        change (0 : ZMod 2) • pairVector 2 3 = pairVector 0 1 at ha
        simpa using ha.symm
      · apply pairVector01_ne_pairVector23.symm
        change (1 : ZMod 2) • pairVector 2 3 = pairVector 0 1 at ha
        simpa using ha
  have hrange : Set.range b = ({pairVector 0 1, pairVector 2 3} : Set V) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [b]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp [b]⟩
      · exact ⟨1, by simp [b]⟩
  rw [show canonicalPlane = Submodule.span (ZMod 2) (Set.range b) by
    simp [canonicalPlane, hrange]]
  rw [finrank_span_eq_card hb]
  decide

theorem pairVector_comm (i j : Ω) : pairVector i j = pairVector j i := by
  apply Subtype.ext
  change (constants Ω).mkQ _ = (constants Ω).mkQ _
  rw [add_comm]

theorem pairVector_add : pairVector 4 5 = pairVector 0 1 + pairVector 2 3 := by
  apply Subtype.ext
  change (constants Ω).mkQ _ = (constants Ω).mkQ _
  apply (Submodule.Quotient.eq (constants Ω)).2
  apply Submodule.subset_span
  change _ = (1 : ZMod 2) • allOne Ω
  ext i
  fin_cases i <;> decide

theorem pairVector_map (g : Equiv.Perm Ω) (i j : Ω) :
    naturalRepresentation Ω g (pairVector i j) = pairVector (g i) (g j) := by
  apply Subtype.ext
  change BinaryPermutation.deletedRepresentation Ω g
      ((constants Ω).mkQ (Pi.single i (1 : ZMod 2) + Pi.single j 1)) = _
  rw [BinaryPermutation.deletedRepresentation_mk]
  apply congrArg (constants Ω).mkQ
  have hsingle (a : Ω) :
      BinaryPermutation.representation Ω g (Pi.single a (1 : ZMod 2)) =
        Pi.single (g a) 1 := by
    ext k
    rw [BinaryPermutation.representation_apply]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases h : g.symm k = a
    · have h' : k = g a := (Equiv.symm_apply_eq g).mp h
      simp [h']
    · have h' : k ≠ g a := by
        intro hk
        apply h
        exact (Equiv.symm_apply_eq g).mpr hk
      simp [h, h']
  rw [map_add, hsingle i, hsingle j]

theorem canonicalLine_map_of_mem {g : Equiv.Perm Ω} (hg : g ∈ H1) :
    Submodule.map (naturalRepresentation Ω g) canonicalLine = canonicalLine := by
  rw [canonicalLine, Submodule.map_span]
  simp only [Set.image_singleton, pairVector_map]
  rcases mem_H1_cases hg with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, pairVector_comm]

theorem pair_mem_base_cases {i j : Ω} (hij : i ≠ j)
    (h : pair i j ∈ baseSyntheme) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  simp only [baseSyntheme, Finset.mem_insert, Finset.mem_singleton] at h
  fin_cases i <;> fin_cases j <;> simp_all [pair] <;>
    rcases h with h | h | h <;> simp_all [Finset.ext_iff] <;>
    (have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3;
      have h4 := h 4; have h5 := h 5; simp_all)

theorem pairVector_mem_canonicalPlane {i j : Ω} (hij : i ≠ j)
    (h : pair i j ∈ baseSyntheme) : pairVector i j ∈ canonicalPlane := by
  have hv01 : pairVector 0 1 ∈ canonicalPlane := Submodule.subset_span (by simp)
  have hv23 : pairVector 2 3 ∈ canonicalPlane := Submodule.subset_span (by simp)
  have hv45 : pairVector 4 5 ∈ canonicalPlane := by
    rw [pairVector_add]
    exact canonicalPlane.add_mem hv01 hv23
  rcases pair_mem_base_cases hij h with h | h | h | h | h | h
  · rw [h.1, h.2]; exact hv01
  · rw [h.1, h.2, pairVector_comm]; exact hv01
  · rw [h.1, h.2]; exact hv23
  · rw [h.1, h.2, pairVector_comm]; exact hv23
  · rw [h.1, h.2]; exact hv45
  · rw [h.1, h.2, pairVector_comm]; exact hv45

theorem canonicalPlane_map_le_of_mem {g : Equiv.Perm Ω} (hg : g ∈ H2) :
    Submodule.map (naturalRepresentation Ω g) canonicalPlane ≤ canonicalPlane := by
  change baseSyntheme.image (fun t => t.image g) = baseSyntheme at hg
  rw [canonicalPlane, Submodule.map_span]
  apply Submodule.span_le.2
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · rw [pairVector_map]
    apply pairVector_mem_canonicalPlane
    · exact g.injective.ne (by decide)
    · change pair (g 0) (g 1) ∈ baseSyntheme
      have hbase : (pair 0 1).image g ∈ baseSyntheme := by
        rw [← hg]
        exact Finset.mem_image.mpr ⟨pair 0 1, by simp [baseSyntheme], rfl⟩
      simpa [pair, Finset.image_insert, Finset.image_singleton] using hbase
  · rw [pairVector_map]
    apply pairVector_mem_canonicalPlane
    · exact g.injective.ne (by decide)
    · change pair (g 2) (g 3) ∈ baseSyntheme
      have hbase : (pair 2 3).image g ∈ baseSyntheme := by
        rw [← hg]
        exact Finset.mem_image.mpr ⟨pair 2 3, by simp [baseSyntheme], rfl⟩
      simpa [pair, Finset.image_insert, Finset.image_singleton] using hbase


private def normalize : Full Ω →ₗ[ZMod 2] Full Ω where
  toFun v := fun i => v i - v 5
  map_add' v w := by ext i; simp; ring
  map_smul' c v := by ext i; simp [mul_sub]

private def coordinates : V →ₗ[ZMod 2] Full Ω :=
  ((constants Ω).liftQ normalize (by
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    ext i
    simp [normalize, allOne])).comp (natural Ω).subtype

@[simp] private theorem coordinates_pair (i j : Ω) :
    coordinates (pairVector i j) = normalize (Pi.single i 1 + Pi.single j 1) := rfl

abbrev Duad := {p : Ω × Ω // p.1 < p.2}
def duadVector (d : Duad) : V := pairVector d.val.1 d.val.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem duad_cert : ∀ d e : Duad,
    normalize (Pi.single d.val.1 1 + Pi.single d.val.2 1) =
      normalize (Pi.single e.val.1 1 + Pi.single e.val.2 1) → d = e := by decide

set_option maxRecDepth 4096 in
private theorem duad_nonzero_cert : ∀ d : Duad,
    normalize (Pi.single d.val.1 1 + Pi.single d.val.2 1) ≠ 0 := by decide

theorem duadVector_injective : Function.Injective duadVector := by
  intro d e h
  exact duad_cert d e (congrArg coordinates h)

theorem duadVector_ne_zero (d : Duad) : duadVector d ≠ 0 := by
  intro h
  apply duad_nonzero_cert d
  simpa [duadVector] using congrArg coordinates h

noncomputable local instance : Fintype V := Fintype.ofFinite V

private theorem card_V : Fintype.card V = 16 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
    finrank_natural_even Ω (by decide)]
  decide

private def vectorCode : Option Duad → V
  | none => 0
  | some d => duadVector d

private theorem vectorCode_injective : Function.Injective vectorCode := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (duadVector_ne_zero b h.symm)
  | some a =>
    cases b with
    | none => exact False.elim (duadVector_ne_zero a h)
    | some b => exact congrArg some (duadVector_injective h)

private theorem vectorCode_surjective : Function.Surjective vectorCode := by
  apply ((Fintype.bijective_iff_injective_and_card vectorCode).2 ⟨vectorCode_injective, ?_⟩).2
  rw [card_V]
  decide

theorem vector_cases (v : V) : v = 0 ∨ ∃ d, v = duadVector d := by
  obtain ⟨a, rfl⟩ := vectorCode_surjective v
  cases a with
  | none => exact Or.inl rfl
  | some d => exact Or.inr ⟨d, rfl⟩

private def sortedDuad (i j : Ω) (hij : i ≠ j) : Duad :=
  if h : i < j then ⟨(i,j), h⟩ else ⟨(j,i), lt_of_le_of_ne (le_of_not_gt h) hij.symm⟩

private theorem sortedDuad_vector (i j : Ω) (hij : i ≠ j) :
    duadVector (sortedDuad i j hij) = pairVector i j := by
  unfold sortedDuad
  split
  · rfl
  · exact pairVector_comm j i

private theorem sortedDuad_pair (i j : Ω) (hij : i ≠ j) :
    pair (sortedDuad i j hij).val.1 (sortedDuad i j hij).val.2 = pair i j := by
  unfold sortedDuad
  split
  · rfl
  · exact Finset.pair_comm j i

set_option maxRecDepth 4096 in
private theorem duad_pair_cert : ∀ d e : Duad,
    pair d.val.1 d.val.2 = pair e.val.1 e.val.2 ↔ d = e := by decide

theorem pairVector_eq_iff {i j k l : Ω} (hij : i ≠ j) (hkl : k ≠ l) :
    pairVector i j = pairVector k l ↔ pair i j = pair k l := by
  rw [← sortedDuad_vector i j hij, ← sortedDuad_vector k l hkl,
    duadVector_injective.eq_iff, ← duad_pair_cert,
    sortedDuad_pair, sortedDuad_pair]

theorem pairVector_ne_zero {i j : Ω} (hij : i ≠ j) : pairVector i j ≠ 0 := by
  rw [← sortedDuad_vector i j hij]
  exact duadVector_ne_zero _

theorem pairVector_mem_line_iff {i j : Ω} (hij : i ≠ j) :
    pairVector i j ∈ canonicalLine ↔ pair i j = pair 4 5 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    fin_cases c
    · change (0 : ZMod 2) • pairVector 4 5 = pairVector i j at hc
      exact False.elim (pairVector_ne_zero hij (by simpa using hc.symm))
    · change (1 : ZMod 2) • pairVector 4 5 = pairVector i j at hc
      exact (pairVector_eq_iff hij (by decide)).mp (by simpa using hc.symm)
  · intro h
    rw [(pairVector_eq_iff hij (by decide)).mpr h]
    exact Submodule.subset_span (by simp)

theorem pairVector_mem_plane_iff {i j : Ω} (hij : i ≠ j) :
    pairVector i j ∈ canonicalPlane ↔ pair i j ∈ baseSyntheme := by
  constructor
  · intro h
    obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp h
    fin_cases a <;> fin_cases b
    all_goals simp only [show (⟨0, by decide⟩ : Fin 2) = (0 : ZMod 2) from rfl,
      show (⟨1, by decide⟩ : Fin 2) = (1 : ZMod 2) from rfl, zero_smul, one_smul, zero_add, add_zero] at h
    · exact False.elim (pairVector_ne_zero hij (by simpa using h.symm))
    · have he := (pairVector_eq_iff hij (by decide : (2 : Ω) ≠ 3)).mp
        (by simpa using h.symm)
      simp [he, baseSyntheme]
    · have he := (pairVector_eq_iff hij (by decide : (0 : Ω) ≠ 1)).mp
        (by simpa using h.symm)
      simp [he, baseSyntheme]
    · have he := (pairVector_eq_iff hij (by decide : (4 : Ω) ≠ 5)).mp
        (by simpa [pairVector_add] using h.symm)
      simp [he, baseSyntheme]
  · exact pairVector_mem_canonicalPlane hij

theorem canonicalLine_stabilizer (g : S) :
    Submodule.map (naturalRepresentation Ω g) canonicalLine = canonicalLine ↔ g ∈ H1 := by
  refine ⟨?_, canonicalLine_map_of_mem⟩
  intro h
  have hv : naturalRepresentation Ω g (pairVector 4 5) ∈ canonicalLine := by
    rw [← h]
    exact Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
  rw [pairVector_map] at hv
  have he := (pairVector_mem_line_iff (g.injective.ne (by decide))).mp hv
  change (pair 4 5).image g = pair 4 5
  simpa [pair] using he

theorem canonicalPlane_stabilizer (g : S) :
    Submodule.map (naturalRepresentation Ω g) canonicalPlane = canonicalPlane ↔ g ∈ H2 := by
  constructor
  · intro h
    change baseSyntheme.image (fun t => t.image g) = baseSyntheme
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      have hp (i j : Ω) (hij : i ≠ j) (hij' : pair i j ∈ baseSyntheme) :
          (pair i j).image g ∈ baseSyntheme := by
        have hv : naturalRepresentation Ω g (pairVector i j) ∈ canonicalPlane := by
          rw [← h]
          exact Submodule.mem_map_of_mem (pairVector_mem_canonicalPlane hij hij')
        rw [pairVector_map] at hv
        simpa [pair] using (pairVector_mem_plane_iff (g.injective.ne hij)).mp hv
      simp only [baseSyntheme, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact hp 0 1 (by decide) (by decide)
      · exact hp 2 3 (by decide) (by decide)
      · exact hp 4 5 (by decide) (by decide)
    · rw [Finset.card_image_of_injective _ (Finset.image_injective g.injective)]
  · intro h
    have hi := canonicalPlane_map_le_of_mem (H2.inv_mem h)
    have hf := Submodule.map_mono (f := naturalRepresentation Ω g) hi
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_eq_id, Submodule.map_id] at hf
    exact le_antisymm (canonicalPlane_map_le_of_mem h) hf


/-- The alternating Borel of the canonical flag. -/
def T0 : Subgroup S := (H1 ⊓ H2) ⊓ alternatingGroup Ω

instance (g : S) : Decidable (g ∈ T0) := by
  change Decidable ((g ∈ H1 ∧ g ∈ H2) ∧ Equiv.Perm.sign g = 1)
  infer_instance

def genA : S := swap01 * swap45
def genB : S := swap23 * swap45
def genC : S := Equiv.swap 0 2 * Equiv.swap 1 3

theorem genA_mem_T0 : genA ∈ T0 := by decide
theorem genB_mem_T0 : genB ∈ T0 := by decide
theorem genC_mem_T0 : genC ∈ T0 := by decide

private def flagWords : List S :=
  [1, genA, genB, genA * genB, genC, genA * genC, genB * genC, genA * genB * genC]

private theorem flagWords_invariant (W : Submodule (ZMod 2) V)
    (ha : Submodule.map (naturalRepresentation Ω genA) W = W)
    (hb : Submodule.map (naturalRepresentation Ω genB) W = W)
    (hc : Submodule.map (naturalRepresentation Ω genC) W = W) :
    ∀ g ∈ flagWords, Submodule.map (naturalRepresentation Ω g) W = W := by
  have hmul (g h : S)
      (hg : Submodule.map (naturalRepresentation Ω g) W = W)
      (hh : Submodule.map (naturalRepresentation Ω h) W = W) :
      Submodule.map (naturalRepresentation Ω (g * h)) W = W := by
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hh, hg]
  intro g hg
  simp only [flagWords, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_one, Module.End.one_eq_id, Submodule.map_id]
  · exact ha
  · exact hb
  · exact hmul _ _ ha hb
  · exact hc
  · exact hmul _ _ ha hc
  · exact hmul _ _ hb hc
  · exact hmul _ _ (hmul _ _ ha hb) hc

private def duadAction (g : S) (d : Duad) : Duad :=
  sortedDuad (g d.val.1) (g d.val.2) (g.injective.ne (ne_of_lt d.property))

private theorem duadAction_vector (g : S) (d : Duad) :
    duadVector (duadAction g d) = naturalRepresentation Ω g (duadVector d) := by
  rw [duadAction, sortedDuad_vector, duadVector, pairVector_map]

private def smallOrbit (d : Duad) : Finset Duad :=
  (flagWords.map (fun g => duadAction g d)).toFinset

private def d01 : Duad := ⟨(0,1), by decide⟩
private def d23 : Duad := ⟨(2,3), by decide⟩
private def d45 : Duad := ⟨(4,5), by decide⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem orbit_line_cert : ∀ d : Duad,
    (smallOrbit d).card ≤ 1 → d = d45 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem orbit_plane_cert : ∀ d : Duad,
    (smallOrbit d).card ≤ 3 → d = d01 ∨ d = d23 ∨ d = d45 := by decide

private theorem orbit_card_bound (W : Submodule (ZMod 2) V)
    (hW : ∀ g ∈ flagWords, Submodule.map (naturalRepresentation Ω g) W = W)
    (d : Duad) (hd : duadVector d ∈ W) :
    (smallOrbit d).card + 1 ≤ 2 ^ Module.finrank (ZMod 2) W := by
  classical
  let f : Option {e // e ∈ smallOrbit d} → W := fun e => match e with
    | none => ⟨0, W.zero_mem⟩
    | some e => ⟨duadVector e.val, by
        obtain ⟨g, hg, he⟩ := List.mem_map.mp (List.mem_toFinset.mp e.property)
        rw [← he, duadAction_vector, ← hW g hg]
        exact Submodule.mem_map_of_mem hd⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (duadVector_ne_zero b.val hab'.symm)
    | some a =>
      cases b with
      | none => exact False.elim (duadVector_ne_zero a.val hab')
      | some b => exact congrArg some (Subtype.ext (duadVector_injective hab'))
  let : Fintype W := Fintype.ofFinite W
  have hc := Fintype.card_le_of_injective f hf
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card] at hc
  simpa only [Fintype.card_option, Fintype.card_coe] using hc

private theorem line_unique_of_words (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 1)
    (hW : ∀ g ∈ flagWords, Submodule.map (naturalRepresentation Ω g) W = W) :
    W = canonicalLine := by
  apply Submodule.eq_of_le_of_finrank_eq _ (hdim.trans canonicalLine_finrank.symm)
  intro v hv
  rcases vector_cases v with rfl | ⟨d, rfl⟩
  · exact canonicalLine.zero_mem
  · have hc := orbit_card_bound W hW d hv
    rw [hdim] at hc
    have he := orbit_line_cert d (by omega)
    rw [he]
    exact Submodule.subset_span (by simp [duadVector, d45])

private theorem plane_unique_of_words (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hW : ∀ g ∈ flagWords, Submodule.map (naturalRepresentation Ω g) W = W) :
    W = canonicalPlane := by
  apply Submodule.eq_of_le_of_finrank_eq _ (hdim.trans canonicalPlane_finrank.symm)
  intro v hv
  rcases vector_cases v with rfl | ⟨d, rfl⟩
  · exact canonicalPlane.zero_mem
  · have hc := orbit_card_bound W hW d hv
    rw [hdim] at hc
    rcases orbit_plane_cert d (by omega) with rfl | rfl | rfl
    · exact pairVector_mem_canonicalPlane (by decide) (by decide)
    · exact pairVector_mem_canonicalPlane (by decide) (by decide)
    · exact pairVector_mem_canonicalPlane (by decide) (by decide)


/-- Three explicit even permutations suffice to determine the invariant line. -/
theorem canonicalLine_unique_of_generators (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 1)
    (ha : Submodule.map (naturalRepresentation Ω genA) W = W)
    (hb : Submodule.map (naturalRepresentation Ω genB) W = W)
    (hc : Submodule.map (naturalRepresentation Ω genC) W = W) :
    W = canonicalLine :=
  line_unique_of_words W hdim (flagWords_invariant W ha hb hc)

/-- Three explicit even permutations suffice to determine the invariant plane. -/
theorem canonicalPlane_unique_of_generators (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (ha : Submodule.map (naturalRepresentation Ω genA) W = W)
    (hb : Submodule.map (naturalRepresentation Ω genB) W = W)
    (hc : Submodule.map (naturalRepresentation Ω genC) W = W) :
    W = canonicalPlane :=
  plane_unique_of_words W hdim (flagWords_invariant W ha hb hc)

theorem canonicalLine_unique (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 1)
    (hW : ∀ g ∈ T0, Submodule.map (naturalRepresentation Ω g) W = W) :
    W = canonicalLine :=
  canonicalLine_unique_of_generators W hdim
    (hW _ genA_mem_T0) (hW _ genB_mem_T0) (hW _ genC_mem_T0)

theorem canonicalPlane_unique (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hW : ∀ g ∈ T0, Submodule.map (naturalRepresentation Ω g) W = W) :
    W = canonicalPlane :=
  canonicalPlane_unique_of_generators W hdim
    (hW _ genA_mem_T0) (hW _ genB_mem_T0) (hW _ genC_mem_T0)

theorem canonicalLine_unique_borel (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 1)
    (hW : ∀ g ∈ H1 ⊓ H2, Submodule.map (naturalRepresentation Ω g) W = W) :
    W = canonicalLine :=
  canonicalLine_unique W hdim (fun g hg => hW g hg.1)

theorem canonicalPlane_unique_borel (W : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hW : ∀ g ∈ H1 ⊓ H2, Submodule.map (naturalRepresentation Ω g) W = W) :
    W = canonicalPlane :=
  canonicalPlane_unique W hdim (fun g hg => hW g hg.1)

/-- Restricting the actual natural representation to `A₆` gives `L1`. -/
theorem canonicalLine_stabilizer_alternating (g : alternatingGroup Ω) :
    Submodule.map (naturalRepresentation Ω (g : S)) canonicalLine = canonicalLine ↔
      (g : S) ∈ L1 := by
  rw [canonicalLine_stabilizer]
  exact ⟨fun h => ⟨h, g.property⟩, fun h => h.1⟩

/-- Restricting the actual natural representation to `A₆` gives `L2`. -/
theorem canonicalPlane_stabilizer_alternating (g : alternatingGroup Ω) :
    Submodule.map (naturalRepresentation Ω (g : S)) canonicalPlane = canonicalPlane ↔
      (g : S) ∈ L2 := by
  rw [canonicalPlane_stabilizer]
  exact ⟨fun h => ⟨h, g.property⟩, fun h => h.1⟩

theorem canonicalLine_le_canonicalPlane : canonicalLine ≤ canonicalPlane := by
  rw [canonicalLine, Submodule.span_le, Set.singleton_subset_iff]
  exact pairVector_mem_canonicalPlane (by decide) (by decide)

theorem canonicalLine_invariant_T0 (g : S) (hg : g ∈ T0) :
    Submodule.map (naturalRepresentation Ω g) canonicalLine = canonicalLine :=
  (canonicalLine_stabilizer g).mpr hg.1.1

theorem canonicalPlane_invariant_T0 (g : S) (hg : g ∈ T0) :
    Submodule.map (naturalRepresentation Ω g) canonicalPlane = canonicalPlane :=
  (canonicalPlane_stabilizer g).mpr hg.1.2


end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
