module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Kernel
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightFaithful
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightSplit
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry

/-!
# The half-weight form on an octad cocode space

The even words on an eight point set, modulo the constant word, carry the
half-weight quadratic form.  Its 28 nonsingular classes are precisely the
classes of duads.  This file transports that concrete form to the supported
space of an arbitrary native octad.  The transport is made through the actual
range and kernel maps of the published cocode construction, so the result is
independent of a chosen coordinate presentation.

Source: Aschbacher--Smith, H.15.2(2--3), printed pp.398--399.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode
namespace MathieuCode.CocodeOctad
noncomputable section

open Atlas.Order20160A8.HalfWeight

abbrev Bit := ZMod 2
abbrev W := Atlas.Order20160A8.DeletedEight.W

def indexEquiv (O : M24LocalGeometry.Octad) : O.val ≃ Fin 8 :=
  Fintype.equivFinOfCardEq (by simp [m24Blocks_card _ O.property])

def reindex (O : M24LocalGeometry.Octad) :
    (O.val → Bit) ≃ₗ[Bit] (Fin 8 → Bit) where
  toFun x i := x ((indexEquiv O).symm i)
  invFun x i := x (indexEquiv O i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

def reindexCore (O : M24LocalGeometry.Octad) :
    BinaryPermutation.core O.val →ₗ[Bit] Atlas.Order20160A8.DeletedEight.evenCode :=
  ((reindex O).toLinearMap.comp (BinaryPermutation.core O.val).subtype).codRestrict _ (by
    intro x
    change ∑ i, x.val ((indexEquiv O).symm i) = 0
    rw [Equiv.sum_comp]
    exact x.property)

private lemma reindexCore_surjective (O : M24LocalGeometry.Octad) :
    Function.Surjective (reindexCore O) := by
  intro x
  refine ⟨⟨fun i => x.val (indexEquiv O i), ?_⟩, ?_⟩
  · change ∑ i, x.val (indexEquiv O i) = 0
    rw [Equiv.sum_comp]
    exact x.property
  · apply Subtype.ext
    ext i
    simp [reindexCore, reindex]

def coreToW (O : M24LocalGeometry.Octad) : BinaryPermutation.core O.val →ₗ[Bit] W :=
  Atlas.Order20160A8.DeletedEight.constants.mkQ.comp (reindexCore O)

lemma coreToW_surjective (O : M24LocalGeometry.Octad) : Function.Surjective (coreToW O) := by
  intro w
  obtain ⟨x, rfl⟩ := Atlas.Order20160A8.DeletedEight.constants.mkQ_surjective w
  obtain ⟨v, rfl⟩ := reindexCore_surjective O x
  exact ⟨v, rfl⟩

private lemma coreToW_ker (O : M24LocalGeometry.Octad) (v : BinaryPermutation.core O.val) :
    v ∈ (coreToW O).ker ↔ v ∈ (BinaryPermutation.constants O.val).comap
      (BinaryPermutation.core O.val).subtype := by
  constructor
  · intro h
    have h' : reindexCore O v ∈ Atlas.Order20160A8.DeletedEight.constants :=
      (Submodule.Quotient.mk_eq_zero Atlas.Order20160A8.DeletedEight.constants).mp h
    change v.val ∈ BinaryPermutation.constants O.val
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h'
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    change c • BinaryPermutation.allOne O.val = v.val
    funext i
    have hh := congrFun (congrArg (fun z : Atlas.Order20160A8.DeletedEight.evenCode => z.val) hc)
      ((indexEquiv O) i)
    simpa [reindexCore, reindex, Atlas.Order20160A8.DeletedEight.oneWord,
      BinaryPermutation.allOne] using hh
  · intro h
    change v.val ∈ BinaryPermutation.constants O.val at h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hv : reindexCore O v ∈ Atlas.Order20160A8.DeletedEight.constants := by
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      change c • Atlas.Order20160A8.DeletedEight.oneWord = reindexCore O v
      apply Subtype.ext
      funext i
      have hh := congrFun hc ((indexEquiv O).symm i)
      simpa [reindexCore, reindex, Atlas.Order20160A8.DeletedEight.oneWord,
        BinaryPermutation.allOne] using hh
    change coreToW O v = 0
    change Submodule.Quotient.mk (reindexCore O v) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv

private lemma coreToNatural_ker (O : M24LocalGeometry.Octad) (v : BinaryPermutation.core O.val) :
    v ∈ (BinaryPermutation.coreToNatural (Ω := O.val)).ker ↔
      v ∈ (BinaryPermutation.constants O.val).comap
        (BinaryPermutation.core O.val).subtype := by
  constructor
  · intro h
    have h0 : BinaryPermutation.coreToNatural (Ω := O.val) v = 0 := h
    have h' := congrArg Subtype.val h0
    change (BinaryPermutation.constants O.val).mkQ v.val = 0 at h'
    change Submodule.Quotient.mk v.val = 0 at h'
    have hv : v.val ∈ BinaryPermutation.constants O.val :=
      (Submodule.Quotient.mk_eq_zero _).mp h'
    change v.val ∈ BinaryPermutation.constants O.val
    exact hv
  · intro h
    change v.val ∈ BinaryPermutation.constants O.val at h
    have hv : (BinaryPermutation.constants O.val).mkQ v.val = 0 := by
      change Submodule.Quotient.mk v.val = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr h
    apply Subtype.ext
    exact hv

def naturalToW (O : M24LocalGeometry.Octad) :
    BinaryPermutation.natural O.val ≃ₗ[Bit] W := by
  let E := (BinaryPermutation.coreToNatural (Ω := O.val)).quotKerEquivOfSurjective
    BinaryPermutation.coreToNatural_surjective
  let F := (coreToW O).quotKerEquivOfSurjective (coreToW_surjective O)
  let e : (BinaryPermutation.coreToNatural (Ω := O.val)).ker = (coreToW O).ker := by
    apply le_antisymm <;> intro v hv
    · rw [coreToW_ker, ← coreToNatural_ker O]
      exact hv
    · rw [coreToNatural_ker O, ← coreToW_ker]
      exact hv
  exact E.symm.trans ((Submodule.quotEquivOfEq _ _ e).trans F)

def spaceToW (O : M24LocalGeometry.Octad) :
    supportedPairSpace O.val ≃ₗ[Bit] W :=
  (naturalEquiv O).symm.trans (naturalToW O)

/-- The transported half-weight form on the supported octad space. -/
def quadratic (O : M24LocalGeometry.Octad) : QuadraticMap Bit (supportedPairSpace O.val) Bit :=
  Atlas.Order20160A8.DeletedEight.quotientQuadratic.comp (spaceToW O).toLinearMap

private lemma duad_halfWeight : ∀ i j : Fin 8, i ≠ j →
    binaryHalfWeight
      ((Pi.single i 1 : Fin 8 → Bit) + (Pi.single j 1 : Fin 8 → Bit)) = 1 := by
  decide +kernel

private lemma weight_two_duad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bit) (hx : hammingNorm x = 2) :
    ∃ i j : ι, i ≠ j ∧ x = Pi.single i 1 + Pi.single j 1 := by
  obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hx
  refine ⟨i, j, hij, ?_⟩
  funext k
  have hk : x k ≠ 0 ↔ k = i ∨ k = j := by
    have : k ∈ Finset.univ.filter (fun a => x a ≠ 0) ↔ k ∈ ({i, j} : Finset ι) := by rw [he]
    simpa using this
  rcases Atlas.Codes.bit_cases (x k) with h | h <;>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp_all

private lemma complement_weight (x : Fin 8 → Bit) :
    hammingNorm x + hammingNorm (x + fun _ => 1) = 8 := by
  rw [Atlas.Codes.hammingNorm_eq_sum, Atlas.Codes.hammingNorm_eq_sum, ← Finset.sum_add_distrib]
  have ht : ∀ a : Bit, (if a = 0 then 0 else 1 : ℕ) +
      (if a + 1 = 0 then 0 else 1) = 1 := by decide
  simp only [Pi.add_apply, ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

private lemma halfWeight_duad_relation (x : Fin 8 → Bit) (hx : (∑ i, x i) = 0)
    (hq : binaryHalfWeight x = 1) :
    ∃ i j : Fin 8, i ≠ j ∧ ∃ a : Bit,
      a • (fun _ : Fin 8 => (1 : Bit)) = x - (Pi.single i 1 + Pi.single j 1) := by
  have hbound : hammingNorm x ≤ 8 := hammingNorm_le_card_fintype
  have heven := (Atlas.Codes.even_weight_iff x).mpr hx
  have hval := congrArg ZMod.val hq
  change (hammingNorm x / 2) % 2 = 1 at hval
  have hw : hammingNorm x = 2 ∨ hammingNorm x = 6 := by
    rw [even_iff_two_dvd] at heven
    omega
  rcases hw with hw | hw
  · obtain ⟨i, j, hij, he⟩ := weight_two_duad x hw
    exact ⟨i, j, hij, 0, by simp [he]⟩
  · have hc := complement_weight x
    obtain ⟨i, j, hij, he⟩ := weight_two_duad (x + fun _ => 1) (by omega)
    refine ⟨i, j, hij, 1, ?_⟩
    rw [← he, one_smul]
    funext k
    change (1 : Bit) = x k - (x k + 1)
    rcases Atlas.Codes.bit_cases (x k) with h | h <;> simp [h]

lemma naturalToW_apply_core (O : M24LocalGeometry.Octad)
    (v : BinaryPermutation.core O.val) :
    naturalToW O (BinaryPermutation.coreToNatural (Ω := O.val) v) = coreToW O v := by
  dsimp [naturalToW]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rw [Submodule.quotEquivOfEq_mk]
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]

lemma spaceToW_apply_core (O : M24LocalGeometry.Octad) (v : BinaryPermutation.core O.val) :
    spaceToW O ⟨toCocode O.val v, by
      let : Nonempty O.val := Fintype.card_pos_iff.mp (by
        rw [Fintype.card_coe, m24Blocks_card _ O.property]
        decide)
      rw [← range_toCocode O.val]
      exact LinearMap.mem_range_self _ _⟩ =
      Atlas.Order20160A8.DeletedEight.constants.mkQ (reindexCore O v) := by
  let u : BinaryPermutation.natural O.val :=
    ⟨toNatural O.val v, by rw [← range_toNatural]; exact LinearMap.mem_range_self _ _⟩
  have hs : naturalEquiv O u =
      ⟨toCocode O.val v, by
        let : Nonempty O.val := Fintype.card_pos_iff.mp (by
          rw [Fintype.card_coe, m24Blocks_card _ O.property]
          decide)
        rw [← range_toCocode O.val]
        exact LinearMap.mem_range_self _ _⟩ := by
    apply Subtype.ext
    exact naturalEquiv_apply O v
  have hu :
      (⟨toCocode O.val v, by
        let : Nonempty O.val := Fintype.card_pos_iff.mp (by
          rw [Fintype.card_coe, m24Blocks_card _ O.property]
          decide)
        rw [← range_toCocode O.val]
        exact LinearMap.mem_range_self _ _⟩ : supportedPairSpace O.val) =
        naturalEquiv O u := by
    apply Subtype.ext
    exact congrArg Subtype.val hs.symm
  change naturalToW O ((naturalEquiv O).symm
    (⟨toCocode O.val v, _⟩ : supportedPairSpace O.val)) = _
  rw [hu, LinearEquiv.symm_apply_apply]
  have huv : u = BinaryPermutation.coreToNatural (Ω := O.val) v := by rfl
  rw [huv]
  exact naturalToW_apply_core O v

lemma quadratic_apply_core (O : M24LocalGeometry.Octad) (v : BinaryPermutation.core O.val) :
    quadratic O (⟨toCocode O.val v, by
      let : Nonempty O.val := Fintype.card_pos_iff.mp (by
        rw [Fintype.card_coe, m24Blocks_card _ O.property]
        decide)
      rw [← range_toCocode O.val]
      exact LinearMap.mem_range_self _ _⟩) =
      Atlas.Order20160A8.HalfWeight.binaryHalfWeight ((reindexCore O v).val) := by
  let : Nonempty O.val := Fintype.card_pos_iff.mp (by
    rw [Fintype.card_coe, m24Blocks_card _ O.property]
    decide)
  let u : supportedPairSpace O.val := ⟨toCocode O.val v, by
    rw [← range_toCocode O.val]
    exact LinearMap.mem_range_self _ _⟩
  change quadratic O u = _
  have hsw : spaceToW O u = Atlas.Order20160A8.DeletedEight.constants.mkQ (reindexCore O v) := by
    apply spaceToW_apply_core
  rw [quadratic, QuadraticMap.comp_apply]
  change Atlas.Order20160A8.DeletedEight.quotientQuadratic (spaceToW O u) = _
  rw [hsw]
  change Atlas.Order20160A8.DeletedEight.quotientQuadratic
    (Submodule.Quotient.mk (reindexCore O v)) = _
  rw [Atlas.Order20160A8.DeletedEight.quotientQuadratic_mk]

lemma quadratic_pair (O : M24LocalGeometry.Octad) {a b : O.val} (hab : a ≠ b) :
    quadratic O (⟨toCocode O.val (starWord O.val a b),
      star_mem_supportedPairSpace O a b⟩) = 1 := by
  let : Nonempty O.val := ⟨a⟩
  let u : supportedPairSpace O.val :=
    ⟨toCocode O.val (starWord O.val a b), star_mem_supportedPairSpace O a b⟩
  change quadratic O u = 1
  have hsw : spaceToW O u =
      Atlas.Order20160A8.DeletedEight.constants.mkQ (reindexCore O (starWord O.val a b)) := by
    apply spaceToW_apply_core
  rw [quadratic, QuadraticMap.comp_apply]
  change Atlas.Order20160A8.DeletedEight.quotientQuadratic (spaceToW O u) = _
  rw [hsw]
  change Atlas.Order20160A8.DeletedEight.quotientQuadratic
    (Submodule.Quotient.mk (reindexCore O (starWord O.val a b))) = _
  rw [Atlas.Order20160A8.DeletedEight.quotientQuadratic_mk]
  change binaryHalfWeight _ = 1
  have h : ∀ i : Fin 8, (reindexCore O (starWord O.val a b)).val i =
      (((Pi.single ((indexEquiv O) a) 1 : Fin 8 → Bit) +
        (Pi.single ((indexEquiv O) b) 1 : Fin 8 → Bit)) i) := by
    intro i
    simp [reindexCore, reindex, starWord, Pi.single_apply, Equiv.symm_apply_eq,
      add_comm]
  rw [show (reindexCore O (starWord O.val a b)).val =
      (Pi.single ((indexEquiv O) a) 1 : Fin 8 → Bit) +
        (Pi.single ((indexEquiv O) b) 1 : Fin 8 → Bit) by funext i; exact h i]
  have hab' : (indexEquiv O) a ≠ (indexEquiv O) b := fun hh => hab ((indexEquiv O).injective hh)
  exact duad_halfWeight _ _ hab'

private lemma quotientQuadratic_nonsingular_iff : ∀ w : W,
    Atlas.Order20160A8.DeletedEight.quotientQuadratic w = 1 ↔
      ∃ i j : Fin 8, i ≠ j ∧
        w = Submodule.Quotient.mk (Atlas.Order20160A8.DeletedEight.duad i j) := by
  intro w
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    rw [Atlas.Order20160A8.DeletedEight.quotientQuadratic_mk]
    constructor
    · intro hx
      obtain ⟨i, j, hij, a, ha⟩ := halfWeight_duad_relation x.val x.property hx
      refine ⟨i, j, hij, (Submodule.Quotient.eq _).mpr ?_⟩
      refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
      apply Subtype.ext
      exact ha
    · rintro ⟨i, j, hij, h⟩
      have he := congrArg Atlas.Order20160A8.DeletedEight.quotientQuadratic h
      rw [Atlas.Order20160A8.DeletedEight.quotientQuadratic_mk,
        Atlas.Order20160A8.DeletedEight.quotientQuadratic_mk] at he
      exact he.trans (duad_halfWeight i j hij)

lemma quadratic_nonsingular_mem_weightTwo (O : M24LocalGeometry.Octad)
    {v : supportedPairSpace O.val} (hv : quadratic O v = 1) :
    v.val ∈ weightTwoOrbit := by
  have hq : Atlas.Order20160A8.DeletedEight.quotientQuadratic (spaceToW O v) = 1 := by
    simpa [quadratic, QuadraticMap.comp_apply] using hv
  obtain ⟨i, j, hij, hw⟩ := (quotientQuadratic_nonsingular_iff (spaceToW O v)).mp hq
  let a : O.val := (indexEquiv O).symm i
  let b : O.val := (indexEquiv O).symm j
  have hab : a ≠ b := by
    intro hab
    apply hij
    calc
      i = (indexEquiv O) a := ((indexEquiv O).apply_symm_apply i).symm
      _ = (indexEquiv O) b := congrArg (indexEquiv O) hab
      _ = j := (indexEquiv O).apply_symm_apply j
  let u : supportedPairSpace O.val :=
    ⟨toCocode O.val (starWord O.val a b), star_mem_supportedPairSpace O a b⟩
  have hu := spaceToW_apply_core O (starWord O.val a b)
  have hreindex : reindexCore O (starWord O.val a b) =
      Atlas.Order20160A8.DeletedEight.duad i j := by
    apply Subtype.ext
    funext k
    simp [reindexCore, reindex, starWord, Atlas.Order20160A8.DeletedEight.duad,
      Atlas.Order20160A8.DeletedEight.duadVector, Pi.single_apply, a, b,
      add_comm]
  have hu' : spaceToW O u =
      Submodule.Quotient.mk (Atlas.Order20160A8.DeletedEight.duad i j) := by
    rw [spaceToW_apply_core, hreindex]
    rfl
  have huv : u = v := (spaceToW O).injective (hu'.trans hw.symm)
  rw [← huv]
  change toCocode O.val (starWord O.val a b) ∈ weightTwoOrbit
  have hstar : starWord O.val a b =
      ⟨Pi.single a 1 + Pi.single b 1, pair_mem_core a b⟩ := by
    apply Subtype.ext
    simp [starWord, add_comm]
  rw [hstar, toCocode_pair _ _ hab]
  exact ⟨_, rfl⟩

lemma quadratic_one_iff_internal_pair (O : M24LocalGeometry.Octad)
    (v : supportedPairSpace O.val) :
    quadratic O v = 1 ↔
      ∃ a b : O.val, a ≠ b ∧
        v.val = toCocode O.val (starWord O.val a b) := by
  constructor
  · intro hv
    have hq : Atlas.Order20160A8.DeletedEight.quotientQuadratic (spaceToW O v) = 1 := by
      simpa [quadratic, QuadraticMap.comp_apply] using hv
    obtain ⟨i, j, hij, hw⟩ :=
      (quotientQuadratic_nonsingular_iff (spaceToW O v)).mp hq
    let a : O.val := (indexEquiv O).symm i
    let b : O.val := (indexEquiv O).symm j
    have hab : a ≠ b := by
      intro hab
      apply hij
      calc
        i = (indexEquiv O) a := ((indexEquiv O).apply_symm_apply i).symm
        _ = (indexEquiv O) b := congrArg (indexEquiv O) hab
        _ = j := (indexEquiv O).apply_symm_apply j
    let u : supportedPairSpace O.val :=
      ⟨toCocode O.val (starWord O.val a b), star_mem_supportedPairSpace O a b⟩
    have hu := spaceToW_apply_core O (starWord O.val a b)
    have hreindex : reindexCore O (starWord O.val a b) =
        Atlas.Order20160A8.DeletedEight.duad i j := by
      apply Subtype.ext
      funext k
      simp [reindexCore, reindex, starWord,
        Atlas.Order20160A8.DeletedEight.duad,
        Atlas.Order20160A8.DeletedEight.duadVector, Pi.single_apply, a, b,
        add_comm]
    have hu' : spaceToW O u =
        Submodule.Quotient.mk (Atlas.Order20160A8.DeletedEight.duad i j) := by
      rw [spaceToW_apply_core, hreindex]
      rfl
    have huv : u = v := (spaceToW O).injective (hu'.trans hw.symm)
    exact ⟨a, b, hab, congrArg Subtype.val huv.symm⟩
  · rintro ⟨a, b, hab, hv⟩
    rw [show v = ⟨toCocode O.val (starWord O.val a b),
      star_mem_supportedPairSpace O a b⟩ from Subtype.ext hv]
    exact quadratic_pair O hab

private lemma isometry_polar {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁]
    [AddCommGroup M₂] [AddCommGroup N] [Module R M₁] [Module R M₂] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (f : Q₁.IsometryEquiv Q₂) (x y : M₁) :
    Q₂.polarBilin (f x) (f y) = Q₁.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  change Q₂ (f x + f y) - Q₂ (f x) - Q₂ (f y) = Q₁ (x + y) - Q₁ x - Q₁ y
  rw [← map_add, f.map_app, f.map_app, f.map_app]

noncomputable def formEquiv (O : M24LocalGeometry.Octad) :
    (ClassicalOrthogonal.formD 3 Bit).IsometryEquiv (quadratic O) := by
  apply QuadraticMap.IsometryEquiv.trans Atlas.Order20160A8.DeletedEight.splitIsometry
  refine ⟨(spaceToW O).symm, ?_⟩
  intro x
  change quadratic O ((spaceToW O).symm x) =
    Atlas.Order20160A8.DeletedEight.quotientQuadratic x
  simp [quadratic, QuadraticMap.comp_apply]

lemma quadratic_polar_nondegenerate (O : M24LocalGeometry.Octad) :
    (quadratic O).polarBilin.Nondegenerate := by
  let e := formEquiv O
  constructor
  · intro v hv
    have hzero : e.symm v = 0 := by
      apply (ClassicalOrthogonal.polarD_nondegenerate (n := 3) (F := Bit)).1
      intro y
      rw [← isometry_polar e]
      simpa using hv (e y)
    apply e.symm.injective
    simpa using hzero
  · intro v hv
    have hzero : e.symm v = 0 := by
      apply (ClassicalOrthogonal.polarD_nondegenerate (n := 3) (F := Bit)).2
      intro y
      rw [← isometry_polar e]
      simpa using hv (e y)
    apply e.symm.injective
    simpa using hzero

lemma m24_avoiding_finrank_le (O : M24LocalGeometry.Octad)
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ supportedPairSpace O.val)
    (ha : Disjoint (I : Set Cocode) weightTwoOrbit) :
    Module.finrank (ZMod 2) I ≤ 3 := by
  let U := supportedPairSpace O.val
  let J := I.comap U.subtype
  have hdim : Module.finrank (ZMod 2) J = Module.finrank (ZMod 2) I := by
    rw [(Submodule.comapSubtypeEquivOfLe hI).finrank_eq]
  have hzero (x : J) : quadratic O x = 0 := by
    by_contra hx
    have hx1 : quadratic O x = 1 := by
      rcases Atlas.Codes.bit_cases (quadratic O x) with h | h
      · exact (hx h).elim
      · exact h
    have hwt := quadratic_nonsingular_mem_weightTwo O hx1
    have hxI : (x : Cocode) ∈ I := x.property
    exact Set.disjoint_left.mp ha hxI hwt
  have htot : J ≤ LinearMap.BilinForm.orthogonal (quadratic O).polarBilin J := by
    intro x hx y hy
    rw [QuadraticMap.polarBilin_apply_apply]
    change quadratic O (y + x) - quadratic O y - quadratic O x = 0
    rw [hzero ⟨y + x, J.add_mem hy hx⟩, hzero ⟨y, hy⟩, hzero ⟨x, hx⟩]
    simp
  have horth : Module.finrank (ZMod 2)
      (LinearMap.BilinForm.orthogonal (quadratic O).polarBilin J) =
      6 - Module.finrank (ZMod 2) J := by
    have hraw := LinearMap.BilinForm.finrank_orthogonal
      (quadratic_polar_nondegenerate O) J
    rw [finrank_supportedPairSpace O] at hraw
    exact hraw
  have hle := Submodule.finrank_mono htot
  rw [horth] at hle
  rw [← hdim]
  omega

end
end MathieuCode.CocodeOctad
