module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
public import Theory.AlgebraicGroup.RootSystems.Classical
public import Theory.AlgebraicGroup.RootSystems.Dynkin

/-!
This module records the standard coordinate root sets and displayed bases for
the exceptional types.  The E-family is cut out from the E₈ model by the
orthogonality conditions defining E₇ and E₆; the index-zero E₈ simple root is
the half-sign vector with six negative coordinates, so its signs have even
negative parity and its pairing with the next simple root is `-1` as required
by the displayed Cartan matrix.  The membership lemmas below are direct
coordinate checks, independent of the later Chevalley-carrier constructions.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Theory.AlgebraicGroup

namespace StandardRootSystem

@[expose]
public noncomputable def typeF4Roots : Set (Vec 4) :=
  pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector

@[expose]
public noncomputable def typeE8Roots : Set (Vec 8) :=
  pairRoots 8 ∪ {x | ∃ ε : Fin 8 → Bool, evenNegative ε ∧ x = halfSignVector ε}

@[expose]
public noncomputable def typeE7Roots : Set (Vec 8) :=
  {x ∈ typeE8Roots | dot x (basisVector 0 + basisVector 1) = 0}

@[expose]
public noncomputable def typeE6Roots : Set (Vec 8) :=
  {x ∈ typeE7Roots | dot x (basisVector 1 - basisVector 2) = 0}

@[expose]
public noncomputable def typeG2Roots (α₁ α₂ : Vec 2) : Set (Vec 2) :=
  {α₁, -α₁, α₂, -α₂,
    α₁ + α₂, -(α₁ + α₂),
    α₁ + 2 • α₂, -(α₁ + 2 • α₂),
    α₁ + 3 • α₂, -(α₁ + 3 • α₂),
    2 • α₁ + 3 • α₂, -(2 • α₁ + 3 • α₂)}

@[expose]
public noncomputable def typeG2SimpleRoot (α₁ α₂ : Vec 2) : Fin 2 → Vec 2
  | ⟨0, _⟩ => α₁
  | ⟨1, _⟩ => α₂

@[expose]
public noncomputable def typeG2LowestRoot (α₁ α₂ : Vec 2) : Vec 2 :=
  -(2 • α₁ + 3 • α₂)

@[expose]
public noncomputable def typeF4SimpleRoot : Fin 4 → Vec 4
  | ⟨0, _⟩ => ![0, 1, -1, 0]
  | ⟨1, _⟩ => ![0, 0, 1, -1]
  | ⟨2, _⟩ => ![0, 0, 0, 1]
  | ⟨3, _⟩ => ![(1 / 2 : ℝ), -(1 / 2), -(1 / 2), -(1 / 2)]

@[expose]
public noncomputable def typeF4LowestRoot : Vec 4 := ![-1, -1, 0, 0]

@[expose]
public noncomputable def typeE8SimpleRoot : Fin 8 → Vec 8
  | ⟨0, _⟩ => ![(1 / 2 : ℝ), -(1 / 2), -(1 / 2), -(1 / 2), -(1 / 2), -(1 / 2), -(1 / 2), (1 / 2)]
  | ⟨1, _⟩ => ![0, 0, 0, 0, 0, 0, 1, -1]
  | ⟨2, _⟩ => ![0, 0, 0, 0, 0, 1, -1, 0]
  | ⟨3, _⟩ => ![0, 0, 0, 0, 0, 0, 1, 1]
  | ⟨4, _⟩ => ![0, 0, 0, 0, 1, -1, 0, 0]
  | ⟨5, _⟩ => ![0, 0, 0, 1, -1, 0, 0, 0]
  | ⟨6, _⟩ => ![0, 0, 1, -1, 0, 0, 0, 0]
  | ⟨7, _⟩ => ![0, 1, -1, 0, 0, 0, 0, 0]

@[expose]
public noncomputable def typeE7SimpleRoot (i : Fin 7) : Vec 8 :=
  typeE8SimpleRoot i.castSucc

@[expose]
public noncomputable def typeE6SimpleRoot (i : Fin 6) : Vec 8 :=
  typeE8SimpleRoot i.castSucc.castSucc

@[expose]
public noncomputable def typeE8LowestRoot : Vec 8 := ![-1, -1, 0, 0, 0, 0, 0, 0]

@[expose]
public noncomputable def typeE7LowestRoot : Vec 8 := ![-1, 1, 0, 0, 0, 0, 0, 0]

@[expose]
public noncomputable def typeE6LowestRoot : Vec 8 :=
  ![-(1 / 2 : ℝ), 1 / 2, 1 / 2, -(1 / 2), -(1 / 2), -(1 / 2), -(1 / 2), -(1 / 2)]

/-- Every half-sign vector belongs to the standard type `F₄` root set. -/
public lemma halfSignVector_mem_typeF4Roots (ε : Fin 4 → Bool) :
    halfSignVector ε ∈ typeF4Roots := by
  simp [typeF4Roots]

/-- A root pairing of type `G₂` has the standard rank-two Dynkin Cartan matrix. -/
public theorem _root_.Theory.AlgebraicGroup.hasDynkinType_g2_of_isG2
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsG2] :
    HasDynkinType P ⟨.G2, 2⟩ := by
  letI := Fintype.ofFinite ι
  let : P.EmbeddedG2 := RootPairing.IsG2.toEmbeddedG2 P
  let s : Set ι :=
    {RootPairing.EmbeddedG2.long P, RootPairing.EmbeddedG2.short P}
  have hli : LinearIndepOn R P.root s := by
    rw [linearIndepOn_iff_image P.root.injective.injOn]
    rw [show P.root '' s = {RootPairing.EmbeddedG2.longRoot P,
      RootPairing.EmbeddedG2.shortRoot P} by simp [s, Set.image_pair]]
    have hv := RootPairing.EmbeddedG2.linearIndependent_short_long P
    have hrange : Set.range ![RootPairing.EmbeddedG2.shortRoot P,
        RootPairing.EmbeddedG2.longRoot P] =
        {RootPairing.EmbeddedG2.longRoot P,
          RootPairing.EmbeddedG2.shortRoot P} := by
      ext x
      simp
    rw [← hrange]
    exact (linearIndepOn_id_range_iff hv.injective).mpr hv
  have hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
      -P.root i ∈ AddSubmonoid.closure (P.root '' s) := by
    intro i
    have hi := RootPairing.EmbeddedG2.mem_allRoots P i
    simp only [RootPairing.EmbeddedG2.allRoots, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    let A : AddSubmonoid M := AddSubmonoid.closure (P.root '' s)
    have hlong : RootPairing.EmbeddedG2.longRoot P ∈ A := by
      apply AddSubmonoid.subset_closure
      exact ⟨RootPairing.EmbeddedG2.long P, by simp [s], rfl⟩
    have hshort : RootPairing.EmbeddedG2.shortRoot P ∈ A := by
      apply AddSubmonoid.subset_closure
      exact ⟨RootPairing.EmbeddedG2.short P, by simp [s], rfl⟩
    have hshortLong : RootPairing.EmbeddedG2.shortAddLongRoot P ∈ A := by
      rw [RootPairing.EmbeddedG2.shortAddLongRoot_eq P]
      exact A.add_mem hshort hlong
    have htwoShortLong : RootPairing.EmbeddedG2.twoShortAddLongRoot P ∈ A := by
      rw [RootPairing.EmbeddedG2.twoShortAddLongRoot_eq P]
      convert A.add_mem (A.nsmul_mem hshort 2) hlong using 1
      all_goals module
    have hthreeShortLong : RootPairing.EmbeddedG2.threeShortAddLongRoot P ∈ A := by
      rw [RootPairing.EmbeddedG2.threeShortAddLongRoot_eq P]
      convert A.add_mem (A.nsmul_mem hshort 3) hlong using 1
      all_goals module
    have hthreeShortTwoLong :
        RootPairing.EmbeddedG2.threeShortAddTwoLongRoot P ∈ A := by
      rw [RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq P]
      convert A.add_mem (A.nsmul_mem hshort 3) (A.nsmul_mem hlong 2) using 1
      all_goals module
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (by rw [h]; exact hlong)
    · exact Or.inr (by simpa [h] using hlong)
    · exact Or.inl (by rw [h]; exact hshort)
    · exact Or.inr (by simpa [h] using hshort)
    · exact Or.inl (by rw [h]; exact hshortLong)
    · exact Or.inr (by simpa [h] using hshortLong)
    · exact Or.inl (by rw [h]; exact htwoShortLong)
    · exact Or.inr (by simpa [h] using htwoShortLong)
    · exact Or.inl (by rw [h]; exact hthreeShortLong)
    · exact Or.inr (by simpa [h] using hthreeShortLong)
    · exact Or.inl (by rw [h]; exact hthreeShortTwoLong)
    · exact Or.inr (by simpa [h] using hthreeShortTwoLong)
  let b : P.Base := RootPairing.Base.mk' P s hli hsp
  have hlong : RootPairing.EmbeddedG2.long P ∈ b.support := by
    change RootPairing.EmbeddedG2.long P ∈ (Set.toFinite s).toFinset
    exact (Set.toFinite s).mem_toFinset.mpr (by simp [s])
  have hshort : RootPairing.EmbeddedG2.short P ∈ b.support := by
    change RootPairing.EmbeddedG2.short P ∈ (Set.toFinite s).toFinset
    exact (Set.toFinite s).mem_toFinset.mpr (by simp [s])
  have hne :
      RootPairing.EmbeddedG2.long P ≠ RootPairing.EmbeddedG2.short P := by
    intro h
    have hp := RootPairing.EmbeddedG2.pairingIn_long_short (P := P)
    rw [h, RootPairing.pairingIn_same] at hp
    norm_num at hp
  have hmem (x : b.support) :
      x.1 = RootPairing.EmbeddedG2.long P ∨
        x.1 = RootPairing.EmbeddedG2.short P := by
    have hx := x.property
    change x.1 ∈ (Set.toFinite s).toFinset at hx
    simpa [s] using (Set.toFinite s).mem_toFinset.mp hx
  let e : b.support ≃ Fin 2 := by
    classical
    let f : b.support → Fin 2 :=
      fun x => if x.1 = RootPairing.EmbeddedG2.short P then 0 else 1
    exact Equiv.ofBijective f (by
      constructor
      · intro i j hij
        rcases hmem i with hi | hi <;> rcases hmem j with hj | hj
        · apply Subtype.ext
          exact hi.trans hj.symm
        · simp [f, hi, hj, hne] at hij
        · simp [f, hi, hj, hne] at hij
        · apply Subtype.ext
          exact hi.trans hj.symm
      · intro x
        fin_cases x
        · exact ⟨⟨RootPairing.EmbeddedG2.short P, hshort⟩, by simp [f]⟩
        · exact ⟨⟨RootPairing.EmbeddedG2.long P, hlong⟩, by simp [f, hne]⟩)
  refine ⟨b, e, ?_⟩
  classical
  have he_short : e ⟨RootPairing.EmbeddedG2.short P, hshort⟩ = 0 := by
    change (if RootPairing.EmbeddedG2.short P = RootPairing.EmbeddedG2.short P then 0 else 1) = 0
    simp
  have he_long : e ⟨RootPairing.EmbeddedG2.long P, hlong⟩ = 1 := by
    change (if RootPairing.EmbeddedG2.long P = RootPairing.EmbeddedG2.short P then 0 else 1) = 1
    simp [hne]
  intro i j
  rcases hmem i with hi | hi <;> rcases hmem j with hj | hj
  · have hi' : i = ⟨RootPairing.EmbeddedG2.long P, hlong⟩ := Subtype.ext hi
    have hj' : j = ⟨RootPairing.EmbeddedG2.long P, hlong⟩ := Subtype.ext hj
    subst i
    subst j
    simp [e, he_short, he_long, dynkinCartanEntry, hne]
  · have hi' : i = ⟨RootPairing.EmbeddedG2.long P, hlong⟩ := Subtype.ext hi
    have hj' : j = ⟨RootPairing.EmbeddedG2.short P, hshort⟩ := Subtype.ext hj
    subst i
    subst j
    simp [e, he_short, he_long, RootPairing.Base.cartanMatrixIn_def,
      dynkinCartanEntry, hne]
  · have hi' : i = ⟨RootPairing.EmbeddedG2.short P, hshort⟩ := Subtype.ext hi
    have hj' : j = ⟨RootPairing.EmbeddedG2.long P, hlong⟩ := Subtype.ext hj
    subst i
    subst j
    simp [e, he_short, he_long, RootPairing.Base.cartanMatrixIn_def,
      dynkinCartanEntry, hne]
  · have hi' : i = ⟨RootPairing.EmbeddedG2.short P, hshort⟩ := Subtype.ext hi
    have hj' : j = ⟨RootPairing.EmbeddedG2.short P, hshort⟩ := Subtype.ext hj
    subst i
    subst j
    simp [e, he_short, he_long, dynkinCartanEntry]

private lemma e6_negative_indices_card :
    (Finset.univ.filter (fun i : Fin 8 => i.val ≠ 1 ∧ i.val ≠ 2)).card = 6 := by
  have hfilter :
      (Finset.univ.filter (fun i : Fin 8 => i.val ≠ 1 ∧ i.val ≠ 2)) =
        ({0, 3, 4, 5, 6, 7} : Finset (Fin 8)) := by
    ext i
    fin_cases i <;> simp
  rw [hfilter]
  simp

/-- The displayed lowest root of the standard type `E6` model belongs to its
root set: it is the half-sign root with six negative entries, orthogonal to
both the E7 and E6 integer conditions. -/
public lemma typeE6LowestRoot_mem_typeE6Roots :
    typeE6LowestRoot ∈ typeE6Roots := by
  let ε : Fin 8 → Bool := fun i => i.val = 1 ∨ i.val = 2
  have hεneg : evenNegative ε := by
    simp [evenNegative, ε]
    change Even (Finset.univ.filter (fun i : Fin 8 => i.val ≠ 1 ∧ i.val ≠ 2)).card
    rw [e6_negative_indices_card]
    exact ⟨3, by norm_num⟩
  constructor
  · constructor
    · right
      refine ⟨ε, hεneg, ?_⟩
      ext i
      fin_cases i <;> simp [typeE6LowestRoot, halfSignVector, ε]
    · simp [dot, basisVector, typeE6LowestRoot, Fin.sum_univ_succ]
  · simp [dot, basisVector, typeE6LowestRoot, Fin.sum_univ_succ]

open Set

/-- The displayed lowest root of the standard type `E7` model belongs to its
root set (it is `-e₀ + e₁`, an E8 pair root satisfying the E7 orthogonality
condition). -/
public lemma typeE7LowestRoot_mem_typeE7Roots :
    typeE7LowestRoot ∈ typeE7Roots := by
  constructor
  · left
    refine ⟨0, 1, ?_, -1, 1, ?_, ?_, ?_⟩
    · intro h
      have hv : (0 : Fin 8).val = (1 : Fin 8).val := congrArg Fin.val h
      norm_num at hv
    · simp
    · simp
    · ext i
      fin_cases i <;> simp [typeE7LowestRoot, basisVector]
  · simp [dot, basisVector, typeE7LowestRoot, Fin.sum_univ_succ]

open Set

/-- The displayed lowest root of the standard type `E8` model belongs to its
root set (it is the negative pair root `-e₀ - e₁`). -/
public lemma typeE8LowestRoot_mem_typeE8Roots :
    typeE8LowestRoot ∈ typeE8Roots := by
  left
  refine ⟨0, 1, ?_, -1, -1, ?_, ?_, ?_⟩
  · intro h
    have hv : (0 : Fin 8).val = (1 : Fin 8).val := congrArg Fin.val h
    norm_num at hv
  · simp
  · simp
  · ext i
    fin_cases i <;> simp [typeE8LowestRoot, basisVector]

open Set

/-- Every non-zero-index E8 simple root is a pair root and hence belongs to
the standard E8 root set. The index-zero half-sign simple root is the only
member whose membership is still blocked by the sign-parity convention. -/
public lemma typeE8SimpleRoot_succ_mem_typeE8Roots :
    ∀ i : Fin 8, 0 < i.val → typeE8SimpleRoot i ∈ typeE8Roots := by
  intro i hi
  left
  fin_cases i
  · exfalso
    simp at hi
  · refine ⟨6, 7, by decide, 1, -1, by simp, by simp, ?_⟩
    ext i; fin_cases i <;> simp [typeE8SimpleRoot, basisVector]
  · refine ⟨5, 6, by decide, 1, -1, by simp, by simp, ?_⟩
    ext i; fin_cases i <;> simp [typeE8SimpleRoot, basisVector]
  · refine ⟨6, 7, by decide, 1, 1, by simp, by simp, ?_⟩
    ext i; fin_cases i <;> simp [typeE8SimpleRoot, basisVector]
  · refine ⟨4, 5, by decide, 1, -1, by simp, by simp, ?_⟩
    ext i; fin_cases i <;> simp [typeE8SimpleRoot, basisVector]
  · refine ⟨3, 4, by decide, 1, -1, by simp, by simp, ?_⟩
    ext i; fin_cases i <;> simp [typeE8SimpleRoot, basisVector]
  · refine ⟨2, 3, by decide, 1, -1, by simp, by simp, ?_⟩
    ext i; fin_cases i <;> simp [typeE8SimpleRoot, basisVector]
  · refine ⟨1, 2, by decide, 1, -1, by simp, by simp, ?_⟩
    ext i; fin_cases i <;> simp [typeE8SimpleRoot, basisVector]

/-- The corrected index-zero vector is an even-parity half-sign root. -/
public lemma typeE8SimpleRoot_zero_mem_typeE8Roots :
    typeE8SimpleRoot 0 ∈ typeE8Roots := by
  right
  let ε : Fin 8 → Bool := fun i => i = 0 ∨ i = 7
  have hεneg : evenNegative ε := by
    simp [evenNegative, ε]
    change Even (Finset.univ.filter (fun i : Fin 8 => i ≠ 0 ∧ i ≠ 7)).card
    have hfilter :
        (Finset.univ.filter (fun i : Fin 8 => i ≠ 0 ∧ i ≠ 7)) =
          ({1, 2, 3, 4, 5, 6} : Finset (Fin 8)) := by
      ext i
      fin_cases i <;> simp
    rw [hfilter]
    have hcard : ({1, 2, 3, 4, 5, 6} : Finset (Fin 8)).card = 6 := by decide
    rw [hcard]
    exact ⟨3, by norm_num⟩
  refine ⟨ε, hεneg, ?_⟩
  ext i
  fin_cases i <;> simp [ε, halfSignVector, typeE8SimpleRoot]

/-- All displayed E8 simple roots are direct members of the standard set. -/
public lemma typeE8SimpleRoot_mem_typeE8Roots :
    ∀ i : Fin 8, typeE8SimpleRoot i ∈ typeE8Roots := by
  intro i
  fin_cases i
  · exact typeE8SimpleRoot_zero_mem_typeE8Roots
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots _ (by simp)
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots _ (by simp)
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots _ (by simp)
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots _ (by simp)
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots _ (by simp)
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots _ (by simp)
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots _ (by simp)

open Set

/-- If a half-sign vector equals the corrected E8 index-zero displayed simple
root, then its sign function is positive exactly at coordinates `0` and `7`.
Thus it has the even negative parity required by `typeE8Roots`. -/
public lemma typeE8SimpleRoot_zero_halfSign_epsilon
    (ε : Fin 8 → Bool)
    (hε : halfSignVector ε = typeE8SimpleRoot 0) :
    ε 0 = true ∧ ε 7 = true ∧ ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → ε i = false := by
  constructor
  · have hval : halfSignVector ε 0 = typeE8SimpleRoot 0 0 := by
      simpa using congrArg (fun v : Vec 8 => v 0) hε
    by_contra hf
    have hhalf : halfSignVector ε 0 = -(1 / 2 : ℝ) := by
      simp [halfSignVector, hf]
    have htype : typeE8SimpleRoot 0 0 = (1 / 2 : ℝ) := by simp [typeE8SimpleRoot]
    have : (1 / 2 : ℝ) = -(1 / 2) := htype.symm.trans (hval.symm.trans hhalf)
    norm_num at this
  · constructor
    · have hval : halfSignVector ε 7 = typeE8SimpleRoot 0 7 := by
        simpa using congrArg (fun v : Vec 8 => v 7) hε
      by_contra hf
      have hhalf : halfSignVector ε 7 = -(1 / 2 : ℝ) := by simp [halfSignVector, hf]
      have htype : typeE8SimpleRoot 0 7 = (1 / 2 : ℝ) := by simp [typeE8SimpleRoot]
      have : (1 / 2 : ℝ) = -(1 / 2) := htype.symm.trans (hval.symm.trans hhalf)
      norm_num at this
    · intro i hi0 hi7
      have hval : halfSignVector ε i = typeE8SimpleRoot 0 i := by
        simpa using congrArg (fun v : Vec 8 => v i) hε
      by_contra ht
      have hhalf : halfSignVector ε i = (1 / 2 : ℝ) := by simp [halfSignVector, ht]
      have htype : typeE8SimpleRoot 0 i = -(1 / 2 : ℝ) := by
        fin_cases i <;> simp_all [typeE8SimpleRoot]
      have : (1 / 2 : ℝ) = -(1 / 2) := hhalf.symm.trans (hval.trans htype)
      norm_num at this

/-- The standard type `F₄` Cartan matrix in the displayed simple-root ordering. -/
@[expose] public def typeF4CartanMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => if i = j then 2
    else if i.val + 1 = j.val then if i.val = 1 then -2 else -1
    else if j.val + 1 = i.val then -1 else 0

open Set

set_option maxHeartbeats 800000 in
private lemma typeF4HalfSignRoot_reflection_pair_mapsTo :
    ∀ r ∈ Set.range halfSignVector,
      MapsTo (fun x => x - (2 * dot r x) • r) (pairRoots 4) typeF4Roots := by
  classical
  let c : Fin 4 → Fin 4 → Fin 4 := fun a b =>
    if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2
  let d : Fin 4 → Fin 4 → Fin 4 := fun a b =>
    if a ≠ 3 ∧ b ≠ 3 then 3 else if a ≠ 2 ∧ b ≠ 2 then 2 else 1
  have hcomplement (a b : Fin 4) (hab : a ≠ b) :
      c a b ≠ a ∧ c a b ≠ b ∧ d a b ≠ a ∧ d a b ≠ b ∧ c a b ≠ d a b ∧
        ∀ j, j = a ∨ j = b ∨ j = c a b ∨ j = d a b := by
    fin_cases a <;> fin_cases b <;> simp_all [c, d]
    all_goals intro j; fin_cases j <;> simp
  intro r hr
  rcases hr with ⟨ε, rfl⟩
  have hdot_basis (i : Fin 4) : dot (halfSignVector ε) (basisVector i) = halfSignVector ε i := by
    simp [dot, basisVector, Pi.single_apply]
  have hdot_add (x y : Vec 4) : dot (halfSignVector ε) (x + y) =
      dot (halfSignVector ε) x + dot (halfSignVector ε) y := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  have hdot_smul (u : ℝ) (x : Vec 4) : dot (halfSignVector ε) (u • x) =
      u * dot (halfSignVector ε) x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  intro x hx
  rcases hx with ⟨a, b, hab, s, t, hs, ht, rfl⟩
  have hdot : dot (halfSignVector ε) (s • basisVector a + t • basisVector b) =
      s * halfSignVector ε a + t * halfSignVector ε b := by
    rw [hdot_add, hdot_smul, hdot_smul, hdot_basis, hdot_basis]
  let q : ℝ := s * halfSignVector ε a + t * halfSignVector ε b
  let y : Vec 4 := s • basisVector a + t • basisVector b -
    (2 * q) • halfSignVector ε
  have horiginal : s • basisVector a + t • basisVector b ∈ pairRoots 4 :=
    ⟨a, b, hab, s, t, hs, ht, rfl⟩
  obtain ⟨hca, hcb, hda, hdb, hcd, hall⟩ := hcomplement a b hab
  change (s • basisVector a + t • basisVector b -
    (2 * dot (halfSignVector ε) (s • basisVector a + t • basisVector b)) •
      halfSignVector ε) ∈ typeF4Roots
  rw [hdot]
  change y ∈ typeF4Roots
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  all_goals
    simp only [one_smul, neg_smul] at hdot ⊢
    cases ha : ε a <;> cases hb : ε b
  all_goals
    by_cases hzero : 2 * q = 0
    · apply Or.inl
      apply Or.inl
      simpa [y, hzero] using horiginal
    · cases hc : ε (c a b) <;> cases hd : ε (d a b)
      all_goals try norm_num [q, halfSignVector, ha, hb] at hzero
      all_goals
        simp only [typeF4Roots, Set.mem_union]
        refine Or.inl (Or.inl ⟨c a b, d a b, hcd, y (c a b), y (d a b), ?_, ?_, ?_⟩)
        · simp [y, q, halfSignVector, basisVector, ha, hb, hc, hca, hcb]
          norm_num
        · simp [y, q, halfSignVector, basisVector, ha, hb, hd, hda, hdb]
          norm_num
        · ext j
          rcases hall j with rfl | rfl | rfl | rfl <;>
            simp [y, q, halfSignVector, basisVector,
              ha, hb, hc, hd, hca, hcb, hda, hdb, hcd, hab, hab.symm,
              eq_comm] <;> norm_num

open Set

/-- Reflection in a half-sign root sends every signed unit root to a type `F₄` root. -/
public lemma typeF4HalfSignRoot_reflection_signedUnit_mapsTo :
    ∀ r ∈ Set.range halfSignVector,
      MapsTo (fun x => x - (2 * dot r x) • r) (signedUnitRoots 4) typeF4Roots := by
  intro r hr
  rcases hr with ⟨ε, rfl⟩
  intro x hx
  rcases hx with ⟨i, rfl | rfl⟩
  · right
    let ε' : Fin 4 → Bool := fun j =>
      if j = i then true else if ε i then !(ε j) else ε j
    refine ⟨ε', ?_⟩
    have hdot : dot (halfSignVector ε) (basisVector i) = halfSignVector ε i := by
      classical
      simp [dot, basisVector, Pi.single_apply]
    change halfSignVector ε' = basisVector i -
      (2 * dot (halfSignVector ε) (basisVector i)) • halfSignVector ε
    rw [hdot]
    ext j
    by_cases hji : j = i
    · subst j
      cases hε : ε i <;> simp [basisVector, halfSignVector, ε', hε] <;> norm_num
    · cases hεi : ε i <;> cases hεj : ε j <;>
        simp [basisVector, halfSignVector, ε', hji, hεi, hεj]
  · right
    let ε' : Fin 4 → Bool := fun j =>
      if j = i then false else if ε i then ε j else !(ε j)
    refine ⟨ε', ?_⟩
    have hdot : dot (halfSignVector ε) (-basisVector i) = -(halfSignVector ε i) := by
      classical
      simp [dot, basisVector, Pi.single_apply]
    change halfSignVector ε' = -basisVector i -
      (2 * dot (halfSignVector ε) (-basisVector i)) • halfSignVector ε
    rw [hdot]
    ext j
    by_cases hji : j = i
    · subst j
      cases hε : ε i <;> simp [basisVector, halfSignVector, ε', hε] <;> norm_num
    · cases hεi : ε i <;> cases hεj : ε j <;>
        simp [basisVector, halfSignVector, ε', hji, hεi, hεj]

public lemma typeF4HalfSignVector_dot (ε δ : Fin 4 → Bool) :
    dot (halfSignVector ε) (halfSignVector δ) =
      (1 / 4 : ℝ) * ∑ i : Fin 4, if ε i = δ i then 1 else -1 := by
  have hprod (i : Fin 4) :
      halfSignVector ε i * halfSignVector δ i =
        if ε i = δ i then (1 / 4 : ℝ) else -(1 / 4 : ℝ) := by
    by_cases h : ε i = δ i
    · cases hi : δ i <;> simp [halfSignVector, h, hi] <;> norm_num
    · cases he : ε i <;> cases hd : δ i <;>
        simp_all [halfSignVector] <;> norm_num
  rw [show dot (halfSignVector ε) (halfSignVector δ) =
      ∑ i : Fin 4, halfSignVector ε i * halfSignVector δ i by rfl]
  simp_rw [hprod]
  simp_rw [show (fun i : Fin 4 =>
      (if ε i = δ i then (1 / 4 : ℝ) else -(1 / 4 : ℝ))) =
      (fun i => (1 / 4 : ℝ) * (if ε i = δ i then 1 else -1)) by
        funext i
        split <;> norm_num]
  rw [← Finset.mul_sum]

open Set

/-- The displayed lowest root of the standard type `F` model belongs to its root set. -/
public lemma typeF4LowestRoot_mem_typeF4Roots :
    typeF4LowestRoot ∈ typeF4Roots := by
  left
  left
  refine ⟨0, 1, ?_, -1, -1, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
  · simp
  · simp
  · ext i
    fin_cases i <;> simp [typeF4LowestRoot, basisVector]

open Set

public lemma typeF4PairRoot_reflection_halfSign_mapsTo : ∀ r ∈ pairRoots 4,
    MapsTo (fun x => x - dot r x • r)
      (Set.range halfSignVector) (Set.range halfSignVector) := by
  classical
  have hdiff_maps (a b : Fin 4) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a - basisVector b) x •
        (basisVector a - basisVector b))
        (Set.range halfSignVector) (Set.range halfSignVector) := by
    intro x hx
    rcases hx with ⟨ε, rfl⟩
    let ε' : Fin 4 → Bool := fun j => ε (Equiv.swap a b j)
    refine ⟨ε', ?_⟩
    have hdot_basis (i : Fin 4) (x : Vec 4) : dot (basisVector i) x = x i := by
      simp [dot, basisVector, Pi.single_apply]
    have hdot : dot (basisVector a - basisVector b) (halfSignVector ε) =
        halfSignVector ε a - halfSignVector ε b := by
      rw [show dot (basisVector a - basisVector b) (halfSignVector ε) =
          dot (basisVector a) (halfSignVector ε) -
            dot (basisVector b) (halfSignVector ε) by
        simp [dot, sub_mul, Finset.sum_sub_distrib]]
      rw [hdot_basis, hdot_basis]
    change halfSignVector ε' = halfSignVector ε -
      dot (basisVector a - basisVector b) (halfSignVector ε) •
        (basisVector a - basisVector b)
    rw [hdot]
    ext j
    by_cases hja : j = a
    · subst j
      cases ha : ε a <;> cases hb : ε b <;>
        simp [ε', halfSignVector, basisVector, hab, ha, hb]
    · by_cases hjb : j = b
      · subst j
        cases ha : ε a <;> cases hb : ε b <;>
          simp [ε', halfSignVector, basisVector, hja, ha, hb]
      · have hswap : Equiv.swap a b j = j :=
          Equiv.swap_apply_of_ne_of_ne hja hjb
        simp [ε', halfSignVector, basisVector, hja, hjb, hswap]
  have hsum_maps (a b : Fin 4) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a + basisVector b) x •
        (basisVector a + basisVector b))
        (Set.range halfSignVector) (Set.range halfSignVector) := by
    intro x hx
    rcases hx with ⟨ε, rfl⟩
    let ε' : Fin 4 → Bool := fun j =>
      if j = a ∨ j = b then !(ε (Equiv.swap a b j)) else ε j
    refine ⟨ε', ?_⟩
    have hdot_basis (i : Fin 4) (x : Vec 4) : dot (basisVector i) x = x i := by
      simp [dot, basisVector, Pi.single_apply]
    have hdot : dot (basisVector a + basisVector b) (halfSignVector ε) =
        halfSignVector ε a + halfSignVector ε b := by
      rw [show dot (basisVector a + basisVector b) (halfSignVector ε) =
          dot (basisVector a) (halfSignVector ε) +
            dot (basisVector b) (halfSignVector ε) by
        simp [dot, add_mul, Finset.sum_add_distrib]]
      rw [hdot_basis, hdot_basis]
    change halfSignVector ε' = halfSignVector ε -
      dot (basisVector a + basisVector b) (halfSignVector ε) •
        (basisVector a + basisVector b)
    rw [hdot]
    ext j
    by_cases hja : j = a
    · subst j
      cases ha : ε a <;> cases hb : ε b <;>
        simp [ε', halfSignVector, basisVector, hab, ha, hb]
    · by_cases hjb : j = b
      · subst j
        cases ha : ε a <;> cases hb : ε b <;>
          simp [ε', halfSignVector, basisVector, hja, ha, hb]
      · simp [ε', halfSignVector, basisVector, hja, hjb]
  have hreflect_neg (r x : Vec 4) :
      x - dot (-r) x • (-r) = x - dot r x • r := by
    have hdot : dot (-r) x = -dot r x := by
      simp [dot, Finset.sum_neg_distrib]
    rw [hdot]
    simp [smul_neg, neg_smul]
  intro r hr
  rcases hr with ⟨a, b, hab, s, t, hs, ht, rfl⟩
  rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
  · simp only [one_smul, neg_smul]
    rw [show -basisVector a + -basisVector b = -(basisVector a + basisVector b) by module]
    intro x hx
    change x - dot (-(basisVector a + basisVector b)) x •
      (-(basisVector a + basisVector b)) ∈ Set.range halfSignVector
    rw [hreflect_neg]
    exact hsum_maps a b hab hx
  · simp only [one_smul, neg_smul]
    rw [show -basisVector a + basisVector b = -(basisVector a - basisVector b) by module]
    intro x hx
    change x - dot (-(basisVector a - basisVector b)) x •
      (-(basisVector a - basisVector b)) ∈ Set.range halfSignVector
    rw [hreflect_neg]
    exact hdiff_maps a b hab hx
  · simp only [one_smul, neg_smul]
    exact hdiff_maps a b hab
  · simp only [one_smul]
    exact hsum_maps a b hab

open Set

public lemma typeF4Roots_span_eq_top :
    Submodule.span ℝ typeF4Roots = (⊤ : Submodule ℝ (Vec 4)) := by
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun ℝ (Fin 4))).mpr
  intro i
  have hi : basisVector i ∈ typeF4Roots := by
    change basisVector i ∈ pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector
    exact Or.inl (Or.inr ⟨i, Or.inl rfl⟩)
  have hspan : basisVector i ∈ Submodule.span ℝ typeF4Roots :=
    Submodule.subset_span hi
  simpa [Pi.basisFun_apply, basisVector] using hspan

open Set

public lemma typeF4SignedUnitRoot_reflection_halfSign_mapsTo : ∀ r ∈ signedUnitRoots 4,
    MapsTo (fun x => x - (2 * dot r x) • r)
      (Set.range halfSignVector) (Set.range halfSignVector) := by
  intro r hr
  rcases hr with ⟨i, rfl | rfl⟩
  · intro x hx
    rcases hx with ⟨ε, rfl⟩
    let ε' : Fin 4 → Bool := fun j => if j = i then !(ε j) else ε j
    refine ⟨ε', ?_⟩
    have hdot : dot (basisVector i) (halfSignVector ε) = halfSignVector ε i := by
      classical
      simp [dot, basisVector, Pi.single_apply]
    change halfSignVector ε' = halfSignVector ε - (2 * dot (basisVector i) (halfSignVector ε)) • basisVector i
    rw [hdot]
    ext j
    by_cases hji : j = i
    · subst j
      cases hε : ε i <;> simp [basisVector, halfSignVector, ε', hε] <;> norm_num
    · cases hε : ε i <;> simp [basisVector, halfSignVector, ε', hji, hε]
  · intro x hx
    rcases hx with ⟨ε, rfl⟩
    let ε' : Fin 4 → Bool := fun j => if j = i then !(ε j) else ε j
    refine ⟨ε', ?_⟩
    have hdot : dot (-basisVector i) (halfSignVector ε) = -(halfSignVector ε i) := by
      classical
      simp [dot, basisVector, Pi.single_apply]
    change halfSignVector ε' = halfSignVector ε -
      (2 * dot (-basisVector i) (halfSignVector ε)) • (-basisVector i)
    rw [hdot]
    ext j
    by_cases hji : j = i
    · subst j
      cases hε : ε i <;> simp [basisVector, halfSignVector, ε', hε] <;> norm_num
    · cases hε : ε i <;> simp [basisVector, halfSignVector, ε', hji, hε]

open Set

/-- Every displayed simple root of the standard type `F₄` model belongs to its root set. -/
public lemma typeF4SimpleRoot_mem_typeF4Roots (i : Fin 4) :
    typeF4SimpleRoot i ∈ typeF4Roots := by
  fin_cases i
  · left
    left
    refine ⟨1, 2, by decide, 1, -1, by simp, by simp, ?_⟩
    ext j
    fin_cases j <;> simp [typeF4SimpleRoot, basisVector]
  · left
    left
    refine ⟨2, 3, by decide, 1, -1, by simp, by simp, ?_⟩
    ext j
    fin_cases j <;> simp [typeF4SimpleRoot, basisVector]
  · left
    right
    exact ⟨3, Or.inl (by
      ext j
      fin_cases j <;> simp [typeF4SimpleRoot, basisVector])⟩
  · right
    let ε : Fin 4 → Bool := fun j => j = 0
    refine ⟨ε, ?_⟩
    ext j
    fin_cases j <;> simp [ε, typeF4SimpleRoot, halfSignVector]

/-- The displayed type `F₄` simple roots have squared norm `2` for the first two long roots
and `1` for the last two short roots. -/
public lemma typeF4SimpleRoot_normSq (i : Fin 4) :
    dot (typeF4SimpleRoot i) (typeF4SimpleRoot i) = if i.val < 2 then 2 else 1 := by
  fin_cases i <;> simp [typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> norm_num

open Set

/-- The displayed lowest root of the standard type `G2` model belongs to its root set. -/
public lemma typeG2LowestRoot_mem_typeG2Roots (α₁ α₂ : Vec 2) :
    typeG2LowestRoot α₁ α₂ ∈ typeG2Roots α₁ α₂ := by
  simp [typeG2LowestRoot, typeG2Roots]

/-- The explicit twelve-element G₂ root set is finite. -/
public lemma typeG2Roots_finite (α₁ α₂ : Vec 2) :
    (typeG2Roots α₁ α₂).Finite := by
  simp [typeG2Roots]

/-- The displayed type `G₂` root set is closed under negation. -/
public lemma typeG2Roots_neg_mem
    (α₁ α₂ x : Vec 2) (hx : x ∈ typeG2Roots α₁ α₂) :
    -x ∈ typeG2Roots α₁ α₂ := by
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [or_left_comm, or_comm]

/-- The standard type `G2` root set is nonempty (it contains `α₁`). -/
public lemma typeG2Roots_nonempty (α₁ α₂ : Vec 2) : (typeG2Roots α₁ α₂).Nonempty :=
  ⟨α₁, by simp [typeG2Roots]⟩

open Set

/-- The displayed simple roots of the standard type `G2` model belong to its root set. -/
public lemma typeG2SimpleRoots_mem_typeG2Roots (α₁ α₂ : Vec 2) :
    α₁ ∈ typeG2Roots α₁ α₂ ∧ α₂ ∈ typeG2Roots α₁ α₂ := by
  simp [typeG2Roots]

/-- The `α₁`-reflection sends `α₂` to `α₁ + α₂` when its coefficient is `-1`. -/
private lemma typeG2_preReflection_alpha1_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h : f α₂ = -1) :
    Module.preReflection α₁ f α₂ = α₁ + α₂ := by
  rw [Module.preReflection_apply, h]
  simp
  abel

/-- The standard type `E6` root set is nonempty (it contains the displayed
lowest root). -/
public lemma typeE6Roots_nonempty : typeE6Roots.Nonempty :=
  ⟨typeE6LowestRoot, typeE6LowestRoot_mem_typeE6Roots⟩

/-- The standard type `E7` root set is nonempty (it contains the displayed
lowest root). -/
public lemma typeE7Roots_nonempty : typeE7Roots.Nonempty :=
  ⟨typeE7LowestRoot, typeE7LowestRoot_mem_typeE7Roots⟩

/-- The standard type `E8` root set is nonempty (it contains the displayed
lowest root). -/
public lemma typeE8Roots_nonempty : typeE8Roots.Nonempty :=
  ⟨typeE8LowestRoot, typeE8LowestRoot_mem_typeE8Roots⟩

open Set

/-- Every non-zero-index E6 simple root is an E8 pair root satisfying both the
E7 and E6 orthogonality conditions, so it belongs to `typeE6Roots`. -/
public lemma typeE6SimpleRoot_pos_mem_typeE6Roots :
    ∀ i : Fin 6, 0 < i.val → typeE6SimpleRoot i ∈ typeE6Roots := by
  intro i hi
  constructor
  · constructor
    · exact typeE8SimpleRoot_succ_mem_typeE8Roots i.castSucc.castSucc hi
    · fin_cases i <;> simp [typeE6SimpleRoot, typeE8SimpleRoot, dot, basisVector,
        Fin.sum_univ_succ]
  · fin_cases i <;> simp [typeE6SimpleRoot, typeE8SimpleRoot, dot, basisVector,
      Fin.sum_univ_succ]

/-- The E6 restriction also contains its index-zero half-sign simple root. -/
public lemma typeE6SimpleRoot_mem_typeE6Roots :
    ∀ i : Fin 6, typeE6SimpleRoot i ∈ typeE6Roots := by
  intro i
  fin_cases i
  · constructor
    · constructor
      · exact typeE8SimpleRoot_zero_mem_typeE8Roots
      · simp [typeE6SimpleRoot, typeE8SimpleRoot, dot, basisVector,
          Fin.sum_univ_succ]
    · simp [typeE6SimpleRoot, typeE8SimpleRoot, dot, basisVector,
        Fin.sum_univ_succ]
  · exact typeE6SimpleRoot_pos_mem_typeE6Roots _ (by simp)
  · exact typeE6SimpleRoot_pos_mem_typeE6Roots _ (by simp)
  · exact typeE6SimpleRoot_pos_mem_typeE6Roots _ (by simp)
  · exact typeE6SimpleRoot_pos_mem_typeE6Roots _ (by simp)
  · exact typeE6SimpleRoot_pos_mem_typeE6Roots _ (by simp)

open Set

/-- Every non-zero-index E7 simple root is an E8 pair root satisfying the E7
orthogonality condition, so it belongs to `typeE7Roots`. -/
public lemma typeE7SimpleRoot_pos_mem_typeE7Roots :
    ∀ i : Fin 7, 0 < i.val → typeE7SimpleRoot i ∈ typeE7Roots := by
  intro i hi
  constructor
  · exact typeE8SimpleRoot_succ_mem_typeE8Roots i.castSucc hi
  · fin_cases i <;> simp [typeE7SimpleRoot, typeE8SimpleRoot, dot, basisVector,
      Fin.sum_univ_succ]

/-- The E7 restriction also contains its index-zero half-sign simple root. -/
public lemma typeE7SimpleRoot_mem_typeE7Roots :
    ∀ i : Fin 7, typeE7SimpleRoot i ∈ typeE7Roots := by
  intro i
  fin_cases i
  · constructor
    · exact typeE8SimpleRoot_zero_mem_typeE8Roots
    · simp [typeE7SimpleRoot, typeE8SimpleRoot, dot, basisVector,
        Fin.sum_univ_succ]
  · exact typeE7SimpleRoot_pos_mem_typeE7Roots _ (by simp)
  · exact typeE7SimpleRoot_pos_mem_typeE7Roots _ (by simp)
  · exact typeE7SimpleRoot_pos_mem_typeE7Roots _ (by simp)
  · exact typeE7SimpleRoot_pos_mem_typeE7Roots _ (by simp)
  · exact typeE7SimpleRoot_pos_mem_typeE7Roots _ (by simp)
  · exact typeE7SimpleRoot_pos_mem_typeE7Roots _ (by simp)

@[expose] public def typeE6CartanMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => if i = j then 2 else if
    (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)
    then -1 else 0

@[expose] public def typeE7CartanMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  fun i j => if i = j then 2 else if
    (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
    (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5)
    then -1 else 0

@[expose] public def typeE8CartanMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => if i = j then 2 else if
    (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
    (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨
    (i.val = 6 ∧ j.val = 7) ∨ (i.val = 7 ∧ j.val = 6)
    then -1 else 0

/-- The corrected half-sign coordinate gives the required adjacent E₈ Cartan
entry: the seventh coordinate contributes the second `-1/2` term. -/
public lemma typeE8SimpleRoot_zero_dot_one :
    dot (typeE8SimpleRoot 0) (typeE8SimpleRoot 1) = (-1 : ℝ) := by
  norm_num [typeE8SimpleRoot, dot, Fin.sum_univ_succ]

@[expose] public def typeG2CartanMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = j then 2 else if i.val = 0 ∧ j.val = 1 then -1 else -3

/-- A four-vertex path with the displayed directed entries is the standard
type `F₄` Cartan matrix.  The hypotheses expose only matrix entries and carry
no classification conclusion. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_pathGraph_eq_typeF4CartanMatrix_of_entries
    {κ : Type*} (A : Matrix κ κ ℤ) (e : Fin 4 ≃ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hforward : ∀ {i j : Fin 4}, i.val + 1 = j.val →
      A (e i) (e j) = if i.val = 1 then -2 else -1)
    (hreverse : ∀ {i j : Fin 4}, j.val + 1 = i.val →
      A (e i) (e j) = -1)
    (hzero : ∀ {i j : Fin 4}, i ≠ j → i.val + 1 ≠ j.val →
      j.val + 1 ≠ i.val → A (e i) (e j) = 0) :
    ∀ i j, A (e i) (e j) = typeF4CartanMatrix i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeF4CartanMatrix] using hdiag i
  by_cases hforward' : i.val + 1 = j.val
  · rw [typeF4CartanMatrix, if_neg hij, if_pos hforward']
    exact hforward hforward'
  by_cases hreverse' : j.val + 1 = i.val
  · rw [typeF4CartanMatrix, if_neg hij, if_neg hforward', if_pos hreverse']
    exact hreverse hreverse'
  rw [typeF4CartanMatrix, if_neg hij, if_neg hforward', if_neg hreverse']
  exact hzero hij hforward' hreverse'

/-- The displayed type `F₄` simple roots have the standard Cartan pairing.
The coroot factor is one for the first two long roots and two for the last two short roots. -/
public lemma typeF4SimpleRoot_pairing (i j : Fin 4) :
    (if j.val < 2 then dot (typeF4SimpleRoot i) (typeF4SimpleRoot j)
      else 2 * dot (typeF4SimpleRoot i) (typeF4SimpleRoot j)) =
      typeF4CartanMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [typeF4CartanMatrix, typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

public lemma typeF4HalfSignRoot_reflection_of_dot_eq_neg_one (ε δ : Fin 4 → Bool)
    (h : dot (halfSignVector ε) (halfSignVector δ) = (-1 : ℝ)) :
    halfSignVector δ -
        (2 * dot (halfSignVector ε) (halfSignVector δ)) • halfSignVector ε ∈
      typeF4Roots := by
  have h0 : ε 0 ≠ δ 0 := by
    intro h0
    rw [typeF4HalfSignVector_dot] at h
    by_cases h1 : ε 1 = δ 1 <;>
      by_cases h2 : ε 2 = δ 2 <;>
        by_cases h3 : ε 3 = δ 3 <;>
          simp [Fin.sum_univ_four, h0, h1, h2, h3] at h <;> norm_num at h
  have h1 : ε 1 ≠ δ 1 := by
    intro h1
    rw [typeF4HalfSignVector_dot] at h
    by_cases h0 : ε 0 = δ 0 <;>
      by_cases h2 : ε 2 = δ 2 <;>
        by_cases h3 : ε 3 = δ 3 <;>
          simp [Fin.sum_univ_four, h0, h1, h2, h3] at h <;> norm_num at h
  have h2 : ε 2 ≠ δ 2 := by
    intro h2
    rw [typeF4HalfSignVector_dot] at h
    by_cases h0 : ε 0 = δ 0 <;>
      by_cases h1 : ε 1 = δ 1 <;>
        by_cases h3 : ε 3 = δ 3 <;>
          simp [Fin.sum_univ_four, h0, h1, h2, h3] at h <;> norm_num at h
  have h3 : ε 3 ≠ δ 3 := by
    intro h3
    rw [typeF4HalfSignVector_dot] at h
    by_cases h0 : ε 0 = δ 0 <;>
      by_cases h1 : ε 1 = δ 1 <;>
        by_cases h2 : ε 2 = δ 2 <;>
          simp [Fin.sum_univ_four, h0, h1, h2, h3] at h <;> norm_num at h
  have heq : halfSignVector δ + (2 : ℝ) • halfSignVector ε = halfSignVector ε := by
    ext i
    fin_cases i
    · cases he : ε 0 <;> cases hd : δ 0
      · exact False.elim (h0 (by simp [he, hd]))
      · simp [halfSignVector, he, hd] ; norm_num
      · simp [halfSignVector, he, hd] ; norm_num
      · exact False.elim (h0 (by simp [he, hd]))
    · cases he : ε 1 <;> cases hd : δ 1
      · exact False.elim (h1 (by simp [he, hd]))
      · simp [halfSignVector, he, hd] ; norm_num
      · simp [halfSignVector, he, hd] ; norm_num
      · exact False.elim (h1 (by simp [he, hd]))
    · cases he : ε 2 <;> cases hd : δ 2
      · exact False.elim (h2 (by simp [he, hd]))
      · simp [halfSignVector, he, hd] ; norm_num
      · simp [halfSignVector, he, hd] ; norm_num
      · exact False.elim (h2 (by simp [he, hd]))
    · cases he : ε 3 <;> cases hd : δ 3
      · exact False.elim (h3 (by simp [he, hd]))
      · simp [halfSignVector, he, hd] ; norm_num
      · simp [halfSignVector, he, hd] ; norm_num
      · exact False.elim (h3 (by simp [he, hd]))
  rw [h]
  norm_num [sub_eq_add_neg]
  have hmem := halfSignVector_mem_typeF4Roots ε
  rw [← heq] at hmem
  exact hmem

public lemma typeF4HalfSignRoot_reflection_of_dot_eq_zero (ε δ : Fin 4 → Bool)
    (h : dot (halfSignVector ε) (halfSignVector δ) = 0) :
    halfSignVector δ -
        (2 * dot (halfSignVector ε) (halfSignVector δ)) • halfSignVector ε ∈
      typeF4Roots := by
  rw [h]
  simpa using halfSignVector_mem_typeF4Roots δ

public lemma typeF4HalfSignRoot_reflection_of_unique_eq
    (ε δ : Fin 4 → Bool) (i : Fin 4)
    (heq : ε i = δ i) (hne : ∀ j, j ≠ i → ε j ≠ δ j) :
    halfSignVector δ -
        (2 * dot (halfSignVector ε) (halfSignVector δ)) • halfSignVector ε ∈
      signedUnitRoots 4 := by
  have hcancel (a b : Bool) (h : a ≠ b) :
      (if b then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) +
          (if a then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) = 0 := by
    cases a <;> cases b <;> simp_all
  fin_cases i
  · have h0 : ε 0 = δ 0 := heq
    have h1 := hne 1 (by decide)
    have h2 := hne 2 (by decide)
    have h3 := hne 3 (by decide)
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = -(1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨0, ?_⟩
    cases he : ε 0 <;> cases hd : δ 0
    · apply Or.inr
      ext j
      fin_cases j
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 1) (δ 1) h1
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 2) (δ 2) h2
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 3) (δ 3) h3
    · simp_all
    · simp_all
    · apply Or.inl
      ext j
      fin_cases j
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 1) (δ 1) h1
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 2) (δ 2) h2
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 3) (δ 3) h3
  · have h0 := hne 0 (by decide)
    have h1 : ε 1 = δ 1 := heq
    have h2 := hne 2 (by decide)
    have h3 := hne 3 (by decide)
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = -(1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨1, ?_⟩
    cases he : ε 1 <;> cases hd : δ 1
    · apply Or.inr
      ext j
      fin_cases j
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 0) (δ 0) h0
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 2) (δ 2) h2
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 3) (δ 3) h3
    · simp_all
    · simp_all
    · apply Or.inl
      ext j
      fin_cases j
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 0) (δ 0) h0
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 2) (δ 2) h2
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 3) (δ 3) h3
  · have h0 := hne 0 (by decide)
    have h1 := hne 1 (by decide)
    have h2 : ε 2 = δ 2 := heq
    have h3 := hne 3 (by decide)
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = -(1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨2, ?_⟩
    cases he : ε 2 <;> cases hd : δ 2
    · apply Or.inr
      ext j
      fin_cases j
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 0) (δ 0) h0
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 1) (δ 1) h1
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 3) (δ 3) h3
    · simp_all
    · simp_all
    · apply Or.inl
      ext j
      fin_cases j
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 0) (δ 0) h0
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 1) (δ 1) h1
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 3) (δ 3) h3
  · have h0 := hne 0 (by decide)
    have h1 := hne 1 (by decide)
    have h2 := hne 2 (by decide)
    have h3 : ε 3 = δ 3 := heq
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = -(1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨3, ?_⟩
    cases he : ε 3 <;> cases hd : δ 3
    · apply Or.inr
      ext j
      fin_cases j
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 0) (δ 0) h0
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 1) (δ 1) h1
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 2) (δ 2) h2
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num
    · simp_all
    · simp_all
    · apply Or.inl
      ext j
      fin_cases j
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 0) (δ 0) h0
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 1) (δ 1) h1
      · simpa [hdot, halfSignVector, basisVector] using hcancel (ε 2) (δ 2) h2
      · simp [hdot, halfSignVector, basisVector, he, hd]; norm_num

public lemma typeF4HalfSignRoot_reflection_of_unique_ne
    (ε δ : Fin 4 → Bool) (i : Fin 4)
    (hne : ε i ≠ δ i) (hsame : ∀ j, j ≠ i → ε j = δ j) :
    halfSignVector δ -
        (2 * dot (halfSignVector ε) (halfSignVector δ)) • halfSignVector ε ∈
      signedUnitRoots 4 := by
  fin_cases i
  · have h0 : ε 0 ≠ δ 0 := hne
    have h1 := hsame 1 (by decide)
    have h2 := hsame 2 (by decide)
    have h3 := hsame 3 (by decide)
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = (1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨0, ?_⟩
    cases he : ε 0 <;> cases hd : δ 0
    · exact False.elim (h0 (by simp_all))
    · apply Or.inl
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h1, h2, h3]; norm_num
    · apply Or.inr
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h1, h2, h3]; norm_num
    · exact False.elim (h0 (by simp_all))
  · have h0 := hsame 0 (by decide)
    have h1 : ε 1 ≠ δ 1 := hne
    have h2 := hsame 2 (by decide)
    have h3 := hsame 3 (by decide)
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = (1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨1, ?_⟩
    cases he : ε 1 <;> cases hd : δ 1
    · exact False.elim (h1 (by simp_all))
    · apply Or.inl
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h0, h2, h3]; norm_num
    · apply Or.inr
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h0, h2, h3]; norm_num
    · exact False.elim (h1 (by simp_all))
  · have h0 := hsame 0 (by decide)
    have h1 := hsame 1 (by decide)
    have h2 : ε 2 ≠ δ 2 := hne
    have h3 := hsame 3 (by decide)
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = (1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨2, ?_⟩
    cases he : ε 2 <;> cases hd : δ 2
    · exact False.elim (h2 (by simp_all))
    · apply Or.inl
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h0, h1, h3]; norm_num
    · apply Or.inr
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h0, h1, h3]; norm_num
    · exact False.elim (h2 (by simp_all))
  · have h0 := hsame 0 (by decide)
    have h1 := hsame 1 (by decide)
    have h2 := hsame 2 (by decide)
    have h3 : ε 3 ≠ δ 3 := hne
    have hdot : dot (halfSignVector ε) (halfSignVector δ) = (1 / 2 : ℝ) := by
      rw [typeF4HalfSignVector_dot]
      simp [Fin.sum_univ_four, h0, h1, h2, h3]
      norm_num
    refine ⟨3, ?_⟩
    cases he : ε 3 <;> cases hd : δ 3
    · exact False.elim (h3 (by simp_all))
    · apply Or.inl
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h0, h1, h2]; norm_num
    · apply Or.inr
      ext j
      fin_cases j <;>
        simp [hdot, halfSignVector, basisVector, he, hd, h0, h1, h2]; norm_num
    · exact False.elim (h3 (by simp_all))

public lemma typeF4HalfSignRoot_reflection_self (ε : Fin 4 → Bool) :
    halfSignVector ε -
        (2 * dot (halfSignVector ε) (halfSignVector ε)) • halfSignVector ε =
      halfSignVector (fun i => !(ε i)) := by
  have hdot : dot (halfSignVector ε) (halfSignVector ε) = 1 := by
    rw [typeF4HalfSignVector_dot]
    norm_num
  rw [hdot]
  ext i
  cases hi : ε i <;> simp [halfSignVector, hi] <;> norm_num

public lemma typeF4HalfSignVector_dot_cases (ε δ : Fin 4 → Bool) :
    dot (halfSignVector ε) (halfSignVector δ) = (-1 : ℝ) ∨
      dot (halfSignVector ε) (halfSignVector δ) = -(1 / 2 : ℝ) ∨
      dot (halfSignVector ε) (halfSignVector δ) = 0 ∨
      dot (halfSignVector ε) (halfSignVector δ) = (1 / 2 : ℝ) ∨
      dot (halfSignVector ε) (halfSignVector δ) = 1 := by
  rw [typeF4HalfSignVector_dot]
  by_cases h0 : ε 0 = δ 0 <;>
    by_cases h1 : ε 1 = δ 1 <;>
      by_cases h2 : ε 2 = δ 2 <;>
        by_cases h3 : ε 3 = δ 3 <;>
          simp [Fin.sum_univ_four, h0, h1, h2, h3] <;> norm_num

public lemma typeF4HalfSignVector_eq_of_dot_eq_one (ε δ : Fin 4 → Bool)
    (hdot : dot (halfSignVector ε) (halfSignVector δ) = 1) :
    ∀ i, ε i = δ i := by
  have hne_false (i : Fin 4) (hne : ε i ≠ δ i) : False := by
    fin_cases i
    · have h0 : ε 0 ≠ δ 0 := by exact hne
      by_cases h1 : ε 1 = δ 1 <;>
      by_cases h2 : ε 2 = δ 2 <;>
      by_cases h3 : ε 3 = δ 3 <;>
      rw [typeF4HalfSignVector_dot] at hdot <;>
      simp [Fin.sum_univ_four, h0, h1, h2, h3] at hdot <;>
      norm_num at hdot
    · have h1 : ε 1 ≠ δ 1 := by exact hne
      by_cases h0 : ε 0 = δ 0 <;>
      by_cases h2 : ε 2 = δ 2 <;>
      by_cases h3 : ε 3 = δ 3 <;>
      rw [typeF4HalfSignVector_dot] at hdot <;>
      simp [Fin.sum_univ_four, h0, h1, h2, h3] at hdot <;>
      norm_num at hdot
    · have h2 : ε 2 ≠ δ 2 := by exact hne
      by_cases h0 : ε 0 = δ 0 <;>
      by_cases h1 : ε 1 = δ 1 <;>
      by_cases h3 : ε 3 = δ 3 <;>
      rw [typeF4HalfSignVector_dot] at hdot <;>
      simp [Fin.sum_univ_four, h0, h1, h2, h3] at hdot <;>
      norm_num at hdot
    · have h3 : ε 3 ≠ δ 3 := by exact hne
      by_cases h0 : ε 0 = δ 0 <;>
      by_cases h1 : ε 1 = δ 1 <;>
      by_cases h2 : ε 2 = δ 2 <;>
      rw [typeF4HalfSignVector_dot] at hdot <;>
      simp [Fin.sum_univ_four, h0, h1, h2, h3] at hdot <;>
      norm_num at hdot
  intro i
  by_contra h
  exact hne_false i h

public lemma typeF4HalfSignVector_exists_unique_eq_of_dot_eq_neg_half
    (ε δ : Fin 4 → Bool)
    (hdot : dot (halfSignVector ε) (halfSignVector δ) = -(1 / 2 : ℝ)) :
    ∃ i, ε i = δ i ∧ ∀ j, j ≠ i → ε j ≠ δ j := by
  rw [typeF4HalfSignVector_dot] at hdot
  by_cases h0 : ε 0 = δ 0 <;>
    by_cases h1 : ε 1 = δ 1 <;>
      by_cases h2 : ε 2 = δ 2 <;>
        by_cases h3 : ε 3 = δ 3
  all_goals
    first
    | refine ⟨0, ?_, ?_⟩
      · exact h0
      · intro j hj
        fin_cases j <;> simp_all
    | refine ⟨1, ?_, ?_⟩
      · exact h1
      · intro j hj
        fin_cases j <;> simp_all
    | refine ⟨2, ?_, ?_⟩
      · exact h2
      · intro j hj
        fin_cases j <;> simp_all
    | refine ⟨3, ?_, ?_⟩
      · exact h3
      · intro j hj
        fin_cases j <;> simp_all
    | simp [Fin.sum_univ_four, h0, h1, h2, h3] at hdot <;> norm_num at hdot

public lemma typeF4HalfSignVector_exists_unique_ne_of_dot_eq_half
    (ε δ : Fin 4 → Bool)
    (h : dot (halfSignVector ε) (halfSignVector δ) = (1 / 2 : ℝ)) :
    ∃ i : Fin 4, ε i ≠ δ i ∧ ∀ j, j ≠ i → ε j = δ j := by
  rw [typeF4HalfSignVector_dot] at h
  by_cases h0 : ε 0 = δ 0 <;>
    by_cases h1 : ε 1 = δ 1 <;>
      by_cases h2 : ε 2 = δ 2 <;>
        by_cases h3 : ε 3 = δ 3 <;>
          simp [Fin.sum_univ_four, h0, h1, h2, h3] at h <;>
          norm_num at h
  · refine ⟨3, h3, ?_⟩
    intro j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact False.elim (hj rfl)
  · refine ⟨2, h2, ?_⟩
    intro j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact False.elim (hj rfl)
    · exact h3
  · refine ⟨1, h1, ?_⟩
    intro j hj
    fin_cases j
    · exact h0
    · exact False.elim (hj rfl)
    · exact h2
    · exact h3
  · refine ⟨0, h0, ?_⟩
    intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact h1
    · exact h2
    · exact h3

open Set

public lemma typeF4Roots_nonempty : Set.Nonempty typeF4Roots :=
  ⟨typeF4LowestRoot, typeF4LowestRoot_mem_typeF4Roots⟩

/-- The displayed type `F₄` simple roots pair to `2` with their coroots.
The coroot factor is one for the first two long roots and two for the last two short roots. -/
public lemma typeF4SimpleRoot_coroot_self_pairing (i : Fin 4) :
    (if i.val < 2 then dot (typeF4SimpleRoot i) (typeF4SimpleRoot i)
      else 2 * dot (typeF4SimpleRoot i) (typeF4SimpleRoot i)) = 2 := by
  rw [typeF4SimpleRoot_normSq]
  split_ifs <;> norm_num

/-- Negation maps the displayed type `G₂` root set to itself. -/
public lemma typeG2Roots_neg_mapsTo (α₁ α₂ : Vec 2) :
    Set.MapsTo Neg.neg (typeG2Roots α₁ α₂) (typeG2Roots α₁ α₂) := by
  intro x hx
  exact typeG2Roots_neg_mem α₁ α₂ x hx

/-- Membership in the displayed type `G₂` root set is invariant under negation. -/
@[simp] public lemma typeG2Roots_neg_mem_iff (α₁ α₂ x : Vec 2) :
    -x ∈ typeG2Roots α₁ α₂ ↔ x ∈ typeG2Roots α₁ α₂ := by
  constructor
  · intro hx
    simpa using typeG2Roots_neg_mem α₁ α₂ (-x) hx
  · exact typeG2Roots_neg_mem α₁ α₂ x

/-- Negation induces a bijective self-map of the displayed type `G₂` root subtype. -/
public lemma typeG2Roots_neg_subtype_bijective (α₁ α₂ : Vec 2) :
    Function.Bijective (fun r : typeG2Roots α₁ α₂ =>
      (⟨-r.1, typeG2Roots_neg_mem α₁ α₂ r.1 r.2⟩ : typeG2Roots α₁ α₂)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact neg_injective (congrArg Subtype.val hxy)
  · intro y
    refine ⟨⟨-y.1, typeG2Roots_neg_mem α₁ α₂ y.1 y.2⟩, ?_⟩
    apply Subtype.ext
    simp

/-- The `α₁`-reflection sends `α₁ + α₂` back to `α₂` for the G₂ coefficients. -/
private lemma typeG2_preReflection_alpha1_add_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = 2) (h₂ : f α₂ = -1) :
    Module.preReflection α₁ f (α₁ + α₂) = α₂ := by
  rw [Module.preReflection_apply]
  rw [map_add, h₁, h₂]
  norm_num

/-- The directed edge relation of the standard simply-laced `E₆` fork. -/
public abbrev _root_.Theory.AlgebraicGroup.typeE6CartanEdge
    (i j : Fin 6) : Prop :=
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
  (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
  (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
  (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
  (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)

/-- The directed edge relation of the standard simply-laced `E₇` fork. -/
public abbrev _root_.Theory.AlgebraicGroup.typeE7CartanEdge
    (i j : Fin 7) : Prop :=
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
  (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
  (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
  (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
  (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
  (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5)

/-- The directed edge relation of the standard simply-laced `E₈` fork. -/
public abbrev _root_.Theory.AlgebraicGroup.typeE8CartanEdge
    (i j : Fin 8) : Prop :=
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
  (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
  (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
  (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
  (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
  (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨
  (i.val = 6 ∧ j.val = 7) ∨ (i.val = 7 ∧ j.val = 6)

/-- A matrix with the displayed `E₆` fork support and simple entries is the
standard type `E₆` Cartan matrix. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_forkGraph_eq_typeE6CartanMatrix_of_entries
    {κ : Type*} (A : Matrix κ κ ℤ) (e : Fin 6 ≃ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hbond : ∀ {i j : Fin 6}, typeE6CartanEdge i j → A (e i) (e j) = -1)
    (hzero : ∀ {i j : Fin 6}, i ≠ j → ¬ typeE6CartanEdge i j →
      A (e i) (e j) = 0) :
    ∀ i j, A (e i) (e j) = typeE6CartanMatrix i j := by
  classical
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeE6CartanMatrix] using hdiag i
  by_cases he : typeE6CartanEdge i j
  · have hb := hbond he
    simp only [typeE6CartanMatrix, if_neg hij]
    change A (e i) (e j) = if typeE6CartanEdge i j then -1 else 0
    simp [he, hb]
  · have hz := hzero hij he
    simp only [typeE6CartanMatrix, if_neg hij]
    change A (e i) (e j) = if typeE6CartanEdge i j then -1 else 0
    simp [he, hz]

/-- A matrix with the displayed `E₇` fork support and simple entries is the
standard type `E₇` Cartan matrix. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_forkGraph_eq_typeE7CartanMatrix_of_entries
    {κ : Type*} (A : Matrix κ κ ℤ) (e : Fin 7 ≃ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hbond : ∀ {i j : Fin 7}, typeE7CartanEdge i j → A (e i) (e j) = -1)
    (hzero : ∀ {i j : Fin 7}, i ≠ j → ¬ typeE7CartanEdge i j →
      A (e i) (e j) = 0) :
    ∀ i j, A (e i) (e j) = typeE7CartanMatrix i j := by
  classical
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeE7CartanMatrix] using hdiag i
  by_cases he : typeE7CartanEdge i j
  · have hb := hbond he
    simp only [typeE7CartanMatrix, if_neg hij]
    change A (e i) (e j) = if typeE7CartanEdge i j then -1 else 0
    simp [he, hb]
  · have hz := hzero hij he
    simp only [typeE7CartanMatrix, if_neg hij]
    change A (e i) (e j) = if typeE7CartanEdge i j then -1 else 0
    simp [he, hz]

/-- A matrix with the displayed `E₈` fork support and simple entries is the
standard type `E₈` Cartan matrix. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_forkGraph_eq_typeE8CartanMatrix_of_entries
    {κ : Type*} (A : Matrix κ κ ℤ) (e : Fin 8 ≃ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hbond : ∀ {i j : Fin 8}, typeE8CartanEdge i j → A (e i) (e j) = -1)
    (hzero : ∀ {i j : Fin 8}, i ≠ j → ¬ typeE8CartanEdge i j →
      A (e i) (e j) = 0) :
    ∀ i j, A (e i) (e j) = typeE8CartanMatrix i j := by
  classical
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeE8CartanMatrix] using hdiag i
  by_cases he : typeE8CartanEdge i j
  · have hb := hbond he
    simp only [typeE8CartanMatrix, if_neg hij]
    change A (e i) (e j) = if typeE8CartanEdge i j then -1 else 0
    simp [he, hb]
  · have hz := hzero hij he
    simp only [typeE8CartanMatrix, if_neg hij]
    change A (e i) (e j) = if typeE8CartanEdge i j then -1 else 0
    simp [he, hz]

/-- A two-element integral Cartan matrix containing a product-three bond can
be oriented and renumbered as the standard `G₂` Cartan matrix. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_rankTwo_tripleBond_isG2
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (a b : κ) (hab : a ≠ b)
    (hprod : A a b * A b a = 3)
    (hcard : Fintype.card κ = 2) :
    ∃ e : Fin 2 ≃ κ,
      ∀ i j, A (e i) (e j) = typeG2CartanMatrix i j := by
  classical
  rcases hrank a b hab with h0 | h11 | h12 | h21 | h13 | h31
  · rcases h0 with ⟨h0, h0'⟩
    norm_num [h0, h0'] at hprod
  · rcases h11 with ⟨h11, h11'⟩
    norm_num [h11, h11'] at hprod
  · rcases h12 with ⟨h12, h12'⟩
    norm_num [h12, h12'] at hprod
  · rcases h21 with ⟨h21, h21'⟩
    norm_num [h21, h21'] at hprod
  · let f : Fin 2 → κ := ![a, b]
    have hinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [hcard]⟩
    let e : Fin 2 ≃ κ := Equiv.ofBijective f hbij
    refine ⟨e, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [e, f, typeG2CartanMatrix]
  · let f : Fin 2 → κ := ![b, a]
    have hinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [hcard]⟩
    let e : Fin 2 ≃ κ := Equiv.ofBijective f hbij
    refine ⟨e, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [e, f, typeG2CartanMatrix]

public lemma typeF4HalfSignRoot_reflection_of_dot_eq_one (ε δ : Fin 4 → Bool)
    (hdot : dot (halfSignVector ε) (halfSignVector δ) = 1) :
    halfSignVector δ -
        (2 * dot (halfSignVector ε) (halfSignVector δ)) • halfSignVector ε ∈
      typeF4Roots := by
  have heq := typeF4HalfSignVector_eq_of_dot_eq_one ε δ hdot
  have hvec : halfSignVector δ = halfSignVector ε := by
    ext i
    simp [halfSignVector, heq i]
  rw [hvec]
  rw [typeF4HalfSignRoot_reflection_self]
  exact halfSignVector_mem_typeF4Roots (fun i => !(ε i))

/-- Negation is a bijection of the displayed type `G₂` root set. -/
public lemma typeG2Roots_neg_bijOn (α₁ α₂ : Vec 2) :
    Set.BijOn Neg.neg (typeG2Roots α₁ α₂) (typeG2Roots α₁ α₂) := by
  refine ⟨typeG2Roots_neg_mapsTo α₁ α₂, ?_, ?_⟩
  · intro x hx y hy hxy
    exact neg_injective hxy
  · intro y hy
    exact ⟨-y, typeG2Roots_neg_mem α₁ α₂ y hy, neg_neg y⟩

/-- The canonical negation equivalence of the displayed type `G₂` root subtype. -/
@[expose] public noncomputable def typeG2RootsNegEquiv (α₁ α₂ : Vec 2) :
    typeG2Roots α₁ α₂ ≃ typeG2Roots α₁ α₂ :=
  Equiv.ofBijective
    (fun r : typeG2Roots α₁ α₂ =>
      (⟨-r.1, typeG2Roots_neg_mem α₁ α₂ r.1 r.2⟩ : typeG2Roots α₁ α₂))
    (typeG2Roots_neg_subtype_bijective α₁ α₂)

/-- The `α₁`-reflection fixes `α₁ + 2 • α₂` for the G₂ coefficients. -/
private lemma typeG2_preReflection_alpha1_add_two_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = 2) (h₂ : f α₂ = -1) :
    Module.preReflection α₁ f (α₁ + 2 • α₂) = α₁ + 2 • α₂ := by
  rw [Module.preReflection_apply]
  rw [map_add, map_nsmul, h₁, h₂]
  norm_num

open Set

public lemma typeF4HalfSignRoot_reflection_halfSign_mapsTo :
    ∀ r ∈ Set.range halfSignVector,
    MapsTo (fun x => x - (2 * dot r x) • r)
      (Set.range halfSignVector) typeF4Roots := by
  intro r hr x hx
  rcases hr with ⟨ε, rfl⟩
  rcases hx with ⟨δ, rfl⟩
  rcases typeF4HalfSignVector_dot_cases ε δ with hnegOne | hnegHalf | hzero | hhalf | hone
  · exact typeF4HalfSignRoot_reflection_of_dot_eq_neg_one ε δ hnegOne
  · obtain ⟨i, heq, hne⟩ :=
      typeF4HalfSignVector_exists_unique_eq_of_dot_eq_neg_half ε δ hnegHalf
    left
    right
    exact typeF4HalfSignRoot_reflection_of_unique_eq ε δ i heq hne
  · exact typeF4HalfSignRoot_reflection_of_dot_eq_zero ε δ hzero
  · obtain ⟨i, hne, heq⟩ :=
      typeF4HalfSignVector_exists_unique_ne_of_dot_eq_half ε δ hhalf
    left
    right
    exact typeF4HalfSignRoot_reflection_of_unique_ne ε δ i hne heq
  · exact typeF4HalfSignRoot_reflection_of_dot_eq_one ε δ hone

/-- The image of the displayed type `G₂` root set under negation is itself. -/
public lemma typeG2Roots_neg_image_eq (α₁ α₂ : Vec 2) :
    Neg.neg '' typeG2Roots α₁ α₂ = typeG2Roots α₁ α₂ :=
  (typeG2Roots_neg_bijOn α₁ α₂).image_eq

/-- The canonical type `G₂` root-subtype equivalence acts by ambient negation. -/
@[simp] public lemma typeG2RootsNegEquiv_apply
    (α₁ α₂ : Vec 2) (r : typeG2Roots α₁ α₂) :
    (typeG2RootsNegEquiv α₁ α₂ r : Vec 2) = -(r : Vec 2) := by
  rfl

/-- The `α₁`-reflection sends `α₁ + 3 • α₂` to `2 • α₁ + 3 • α₂`. -/
private lemma typeG2_preReflection_alpha1_add_three_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = 2) (h₂ : f α₂ = -1) :
    Module.preReflection α₁ f (α₁ + 3 • α₂) = 2 • α₁ + 3 • α₂ := by
  rw [Module.preReflection_apply]
  rw [map_add, map_nsmul, h₁, h₂]
  norm_num
  ext i
  simp only [Pi.add_apply, Pi.mul_apply]
  simp
  ring

open Set

/-- Reflection in a pair root preserves the standard type `F₄` root set. -/
public lemma typeF4PairRoot_reflection_mapsTo : ∀ r ∈ pairRoots 4,
    MapsTo (fun x => x - dot r x • r) typeF4Roots typeF4Roots := by
  intro r hr x hx
  rcases hx with hx | hx
  · left
    exact (typeBRoot_reflection_mapsTo 4).1 r hr hx
  · right
    exact typeF4PairRoot_reflection_halfSign_mapsTo r hr hx

open Set

/-- Reflection in a signed unit root preserves the displayed type `F₄` root set. -/
public lemma typeF4SignedUnitRoot_reflection_mapsTo : ∀ r ∈ signedUnitRoots 4,
    MapsTo (fun x => x - (2 * dot r x) • r) typeF4Roots typeF4Roots := by
  intro r hr x hx
  rcases hx with hx | hx
  · left
    exact (typeBRoot_reflection_mapsTo 4).2 r hr hx
  · right
    exact typeF4SignedUnitRoot_reflection_halfSign_mapsTo r hr hx

open Set

public lemma typeF4HalfSignRoot_reflection_mapsTo :
    ∀ r ∈ Set.range halfSignVector,
      MapsTo (fun x => x - (2 * dot r x) • r) typeF4Roots typeF4Roots := by
  intro r hr x hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · exact (typeF4HalfSignRoot_reflection_pair_mapsTo r hr) hx
    · exact (typeF4HalfSignRoot_reflection_signedUnit_mapsTo r hr) hx
  · exact (typeF4HalfSignRoot_reflection_halfSign_mapsTo r hr) hx

/-- The `α₁`-reflection sends `2 • α₁ + 3 • α₂` to `α₁ + 3 • α₂`. -/
private lemma typeG2_preReflection_two_alpha1_add_three_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = 2) (h₂ : f α₂ = -1) :
    Module.preReflection α₁ f (2 • α₁ + 3 • α₂) = α₁ + 3 • α₂ := by
  rw [Module.preReflection_apply]
  rw [map_add, map_nsmul, map_nsmul, h₁, h₂]
  norm_num
  ext i
  simp only [Pi.add_apply, Pi.mul_apply]
  simp
  ring

open Set

/-- Reflection in any displayed type `F₄` root preserves the full root set,
using the long-root formula on pair roots and the short-root formula otherwise. -/
public lemma typeF4Root_reflection_mapsTo :
    ∀ r ∈ typeF4Roots,
      MapsTo
        (fun x => @ite (Vec 4) (r ∈ pairRoots 4) (Classical.propDecidable _)
          (x - dot r x • r) (x - (2 * dot r x) • r))
        typeF4Roots typeF4Roots := by
  classical
  intro r hr
  rcases hr with hr | hr
  · rcases hr with hrPair | hrUnit
    · simpa [hrPair] using typeF4PairRoot_reflection_mapsTo r hrPair
    · by_cases hrPair : r ∈ pairRoots 4
      · simpa [hrPair] using typeF4PairRoot_reflection_mapsTo r hrPair
      · simpa [hrPair] using typeF4SignedUnitRoot_reflection_mapsTo r hrUnit
  · by_cases hrPair : r ∈ pairRoots 4
    · simpa [hrPair] using typeF4PairRoot_reflection_mapsTo r hrPair
    · simpa [hrPair] using typeF4HalfSignRoot_reflection_mapsTo r hr

/-- The `α₁` pre-reflection preserves the explicit type `G₂` root set. -/
private lemma typeG2_preReflection_alpha1_mapsTo
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = 2) (h₂ : f α₂ = -1) :
    Set.MapsTo (Module.preReflection α₁ f)
      (typeG2Roots α₁ α₂) (typeG2Roots α₁ α₂) := by
  intro x hx
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Module.preReflection_apply_self h₁]
    simp
  · rw [map_neg, Module.preReflection_apply_self h₁]
    simp
  · rw [typeG2_preReflection_alpha1_alpha2 h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha1_alpha2 h₂]
    simp
  · rw [typeG2_preReflection_alpha1_add_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha1_add_alpha2 h₁ h₂]
    simp
  · rw [typeG2_preReflection_alpha1_add_two_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha1_add_two_alpha2 h₁ h₂]
    simp
  · rw [typeG2_preReflection_alpha1_add_three_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha1_add_three_alpha2 h₁ h₂]
    simp
  · rw [typeG2_preReflection_two_alpha1_add_three_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_two_alpha1_add_three_alpha2 h₁ h₂]
    simp

/-- The `α₂`-reflection sends `α₁` to `α₁ + 3 • α₂` for the G₂ coefficient `-3`. -/
private lemma typeG2_preReflection_alpha2_alpha1
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h : f α₁ = -3) :
    Module.preReflection α₂ f α₁ = α₁ + 3 • α₂ := by
  rw [Module.preReflection_apply, h]
  simp
  ext i
  simp

/-- The `α₂`-reflection sends `α₁ + 3 • α₂` back to `α₁`. -/
private lemma typeG2_preReflection_alpha2_alpha1_add_three_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = -3) (h₂ : f α₂ = 2) :
    Module.preReflection α₂ f (α₁ + 3 • α₂) = α₁ := by
  rw [Module.preReflection_apply]
  rw [map_add, map_nsmul, h₁, h₂]
  norm_num
  ext i
  simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]

/-- The `α₂`-reflection sends `α₁ + α₂` to `α₁ + 2 • α₂`. -/
private lemma typeG2_preReflection_alpha2_alpha1_add_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = -3) (h₂ : f α₂ = 2) :
    Module.preReflection α₂ f (α₁ + α₂) = α₁ + 2 • α₂ := by
  rw [Module.preReflection_apply]
  rw [map_add, h₁, h₂]
  norm_num
  ext i
  simp only [Pi.add_apply, Pi.mul_apply]
  simp
  ring

/-- The `α₂`-reflection sends `α₁ + 2 • α₂` to `α₁ + α₂`. -/
private lemma typeG2_preReflection_alpha2_alpha1_add_two_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = -3) (h₂ : f α₂ = 2) :
    Module.preReflection α₂ f (α₁ + 2 • α₂) = α₁ + α₂ := by
  rw [Module.preReflection_apply]
  rw [map_add, map_nsmul, h₁, h₂]
  norm_num
  ext i
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- The `α₂`-reflection fixes the highest G₂ root for the standard coefficients. -/
private lemma typeG2_preReflection_alpha2_two_alpha1_add_three_alpha2
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = -3) (h₂ : f α₂ = 2) :
    Module.preReflection α₂ f (2 • α₁ + 3 • α₂) = 2 • α₁ + 3 • α₂ := by
  rw [Module.preReflection_apply]
  rw [map_add, map_nsmul, map_nsmul, h₁, h₂]
  norm_num

/-- The `α₂` pre-reflection preserves the explicit type `G₂` root set. -/
private lemma typeG2_preReflection_alpha2_mapsTo
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = -3) (h₂ : f α₂ = 2) :
    Set.MapsTo (Module.preReflection α₂ f)
      (typeG2Roots α₁ α₂) (typeG2Roots α₁ α₂) := by
  intro x hx
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [typeG2_preReflection_alpha2_alpha1 h₁]
    simp
  · rw [map_neg, typeG2_preReflection_alpha2_alpha1 h₁]
    simp
  · rw [Module.preReflection_apply_self h₂]
    simp
  · rw [map_neg, Module.preReflection_apply_self h₂]
    simp
  · rw [typeG2_preReflection_alpha2_alpha1_add_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha2_alpha1_add_alpha2 h₁ h₂]
    simp
  · rw [typeG2_preReflection_alpha2_alpha1_add_two_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha2_alpha1_add_two_alpha2 h₁ h₂]
    simp
  · rw [typeG2_preReflection_alpha2_alpha1_add_three_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha2_alpha1_add_three_alpha2 h₁ h₂]
    simp
  · rw [typeG2_preReflection_alpha2_two_alpha1_add_three_alpha2 h₁ h₂]
    simp
  · rw [map_neg, typeG2_preReflection_alpha2_two_alpha1_add_three_alpha2 h₁ h₂]
    simp

/-- The canonical root embedding of the explicit type `G₂` root subtype. -/
@[expose] public noncomputable def typeG2RootEmbedding
    (α₁ α₂ : Vec 2) : typeG2Roots α₁ α₂ ↪ Vec 2 :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The canonical G₂ root embedding intertwines subtype negation with ambient negation. -/
@[simp] public lemma typeG2RootEmbedding_neg_apply
    (α₁ α₂ : Vec 2) (r : typeG2Roots α₁ α₂) :
    typeG2RootEmbedding α₁ α₂ (typeG2RootsNegEquiv α₁ α₂ r) =
      -typeG2RootEmbedding α₁ α₂ r :=
  typeG2RootsNegEquiv_apply α₁ α₂ r

/-- The canonical type `G₂` root embedding has exactly the displayed root set as range. -/
public lemma typeG2RootEmbedding_range (α₁ α₂ : Vec 2) :
    Set.range (typeG2RootEmbedding α₁ α₂) = typeG2Roots α₁ α₂ := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact r.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Package explicit coroot-side data into a G₂ root pairing without hiding any hypotheses. -/
public theorem typeG2RootPairing_exists
    (α₁ α₂ : Vec 2) {N : Type*} [AddCommGroup N] [Module ℝ N]
    (p : Vec 2 →ₗ[ℝ] N →ₗ[ℝ] ℝ) [p.IsPerfPair]
    (coroot : typeG2Roots α₁ α₂ ↪ N)
    (hp : ∀ r, p (typeG2RootEmbedding α₁ α₂ r) (coroot r) = 2)
    (hs : ∀ r, Set.MapsTo
      (Module.preReflection (typeG2RootEmbedding α₁ α₂ r)
        (p.flip (coroot r)))
      (Set.range (typeG2RootEmbedding α₁ α₂))
      (Set.range (typeG2RootEmbedding α₁ α₂)))
    (hsp : Submodule.span ℝ (Set.range (typeG2RootEmbedding α₁ α₂)) = ⊤) :
    ∃ P : RootPairing (typeG2Roots α₁ α₂) ℝ (Vec 2) N,
      P.root = typeG2RootEmbedding α₁ α₂ ∧ P.coroot = coroot := by
  letI := Set.Finite.fintype (typeG2Roots_finite α₁ α₂)
  refine ⟨RootPairing.mk'' p (typeG2RootEmbedding α₁ α₂) coroot hp hs hsp, ?_, ?_⟩
  · rfl
  · rfl

/-- The `α₁` pre-reflection preserves the range of the canonical G₂ root embedding. -/
public lemma typeG2RootEmbedding_preReflection_alpha1_mapsTo
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = 2) (h₂ : f α₂ = -1) :
    Set.MapsTo (Module.preReflection α₁ f)
      (Set.range (typeG2RootEmbedding α₁ α₂))
      (Set.range (typeG2RootEmbedding α₁ α₂)) := by
  simpa only [typeG2RootEmbedding_range] using
    (typeG2_preReflection_alpha1_mapsTo h₁ h₂)

/-- The `α₂` pre-reflection preserves the range of the canonical G₂ root embedding. -/
public lemma typeG2RootEmbedding_preReflection_alpha2_mapsTo
    {α₁ α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = -3) (h₂ : f α₂ = 2) :
    Set.MapsTo (Module.preReflection α₂ f)
      (Set.range (typeG2RootEmbedding α₁ α₂))
      (Set.range (typeG2RootEmbedding α₁ α₂)) := by
  simpa only [typeG2RootEmbedding_range] using
    (typeG2_preReflection_alpha2_mapsTo h₁ h₂)

/-- If the two displayed simple roots span `Vec 2`, so does the canonical G₂ root family. -/
public lemma typeG2RootEmbedding_span_eq_top_of_simpleRoots
    (α₁ α₂ : Vec 2)
    (hspan : Submodule.span ℝ ({α₁, α₂} : Set (Vec 2)) = ⊤) :
    Submodule.span ℝ (Set.range (typeG2RootEmbedding α₁ α₂)) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hα₁ : α₁ ∈ Set.range (typeG2RootEmbedding α₁ α₂) :=
    ⟨⟨α₁, (typeG2SimpleRoots_mem_typeG2Roots α₁ α₂).1⟩, rfl⟩
  have hα₂ : α₂ ∈ Set.range (typeG2RootEmbedding α₁ α₂) :=
    ⟨⟨α₂, (typeG2SimpleRoots_mem_typeG2Roots α₁ α₂).2⟩, rfl⟩
  rcases hx with h | h
  · simpa [h] using hα₁
  · simpa [h] using hα₂

/-- The two displayed G₂ simple roots lie in the canonical embedding range. -/
private lemma typeG2SimpleRoots_mem_embeddingRange (α₁ α₂ : Vec 2) :
    α₁ ∈ Set.range (typeG2RootEmbedding α₁ α₂) ∧
      α₂ ∈ Set.range (typeG2RootEmbedding α₁ α₂) := by
  constructor
  · exact ⟨⟨α₁, (typeG2SimpleRoots_mem_typeG2Roots α₁ α₂).1⟩, rfl⟩
  · exact ⟨⟨α₂, (typeG2SimpleRoots_mem_typeG2Roots α₁ α₂).2⟩, rfl⟩

/-- The packaged G₂ pairing supplies coreflection closure of its coroot range. -/
private lemma typeG2RootPairingCoreflectionClosure
    (α₁ α₂ : Vec 2) {N : Type*} [AddCommGroup N] [Module ℝ N]
    (p : Vec 2 →ₗ[ℝ] N →ₗ[ℝ] ℝ) [p.IsPerfPair]
    (coroot : typeG2Roots α₁ α₂ ↪ N)
    (hp : ∀ r, p (typeG2RootEmbedding α₁ α₂ r) (coroot r) = 2)
    (hs : ∀ r, Set.MapsTo
      (Module.preReflection (typeG2RootEmbedding α₁ α₂ r)
        (p.flip (coroot r)))
      (Set.range (typeG2RootEmbedding α₁ α₂))
      (Set.range (typeG2RootEmbedding α₁ α₂)))
    (hsp : Submodule.span ℝ (Set.range (typeG2RootEmbedding α₁ α₂)) = ⊤) :
    ∃ P : RootPairing (typeG2Roots α₁ α₂) ℝ (Vec 2) N,
      P.root = typeG2RootEmbedding α₁ α₂ ∧ P.coroot = coroot ∧
        ∀ r, Set.MapsTo (P.coreflection r)
          (Set.range P.coroot) (Set.range P.coroot) := by
  rcases typeG2RootPairing_exists α₁ α₂ p coroot hp hs hsp with
    ⟨P, hroot, hcoroot⟩
  refine ⟨P, hroot, hcoroot, ?_⟩
  intro r
  exact P.mapsTo_coreflection_coroot r

/-- The packaged G₂ root pairing exposes its original root--coroot pairing formula. -/
private lemma typeG2RootPairingFormula
    (α₁ α₂ : Vec 2) {N : Type*} [AddCommGroup N] [Module ℝ N]
    (p : Vec 2 →ₗ[ℝ] N →ₗ[ℝ] ℝ) [p.IsPerfPair]
    (coroot : typeG2Roots α₁ α₂ ↪ N)
    (hp : ∀ r, p (typeG2RootEmbedding α₁ α₂ r) (coroot r) = 2)
    (hs : ∀ r, Set.MapsTo
      (Module.preReflection (typeG2RootEmbedding α₁ α₂ r)
        (p.flip (coroot r)))
      (Set.range (typeG2RootEmbedding α₁ α₂))
      (Set.range (typeG2RootEmbedding α₁ α₂)))
    (hsp : Submodule.span ℝ (Set.range (typeG2RootEmbedding α₁ α₂)) = ⊤) :
    ∃ P : RootPairing (typeG2Roots α₁ α₂) ℝ (Vec 2) N,
      P.root = typeG2RootEmbedding α₁ α₂ ∧ P.coroot = coroot ∧
        ∀ r s, (P.toLinearMap (P.root r)) (P.coroot s) = P.pairing r s := by
  rcases typeG2RootPairing_exists α₁ α₂ p coroot hp hs hsp with
    ⟨P, hroot, hcoroot⟩
  refine ⟨P, hroot, hcoroot, ?_⟩
  intro r s
  exact P.root_coroot_eq_pairing r s

/-- The packaged G₂ root pairing has diagonal pairing value `2`. -/
private lemma typeG2RootPairingDiagonal
    (α₁ α₂ : Vec 2) {N : Type*} [AddCommGroup N] [Module ℝ N]
    (p : Vec 2 →ₗ[ℝ] N →ₗ[ℝ] ℝ) [p.IsPerfPair]
    (coroot : typeG2Roots α₁ α₂ ↪ N)
    (hp : ∀ r, p (typeG2RootEmbedding α₁ α₂ r) (coroot r) = 2)
    (hs : ∀ r, Set.MapsTo
      (Module.preReflection (typeG2RootEmbedding α₁ α₂ r)
        (p.flip (coroot r)))
      (Set.range (typeG2RootEmbedding α₁ α₂))
      (Set.range (typeG2RootEmbedding α₁ α₂)))
    (hsp : Submodule.span ℝ (Set.range (typeG2RootEmbedding α₁ α₂)) = ⊤) :
    ∃ P : RootPairing (typeG2Roots α₁ α₂) ℝ (Vec 2) N,
      P.root = typeG2RootEmbedding α₁ α₂ ∧ P.coroot = coroot ∧
        ∀ r, P.pairing r r = 2 := by
  rcases typeG2RootPairing_exists α₁ α₂ p coroot hp hs hsp with
    ⟨P, hroot, hcoroot⟩
  refine ⟨P, hroot, hcoroot, ?_⟩
  intro r
  rw [← P.root_coroot_eq_pairing]
  exact P.root_coroot_two r

/-- The α₁ pre-reflection is involutive once its self-coefficient is `2`. -/
public lemma typeG2RootEmbedding_preReflection_alpha1_involutive
    {α₁ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₁ : f α₁ = 2) :
    Function.Involutive (Module.preReflection α₁ f) :=
  Module.involutive_preReflection h₁

/-- The α₂ pre-reflection is involutive once its self-coefficient is `2`. -/
public lemma typeG2RootEmbedding_preReflection_alpha2_involutive
    {α₂ : Vec 2} {f : Vec 2 →ₗ[ℝ] ℝ}
    (h₂ : f α₂ = 2) :
    Function.Involutive (Module.preReflection α₂ f) :=
  Module.involutive_preReflection h₂

/-- Package explicit coroot-side G₂ data when the displayed simple roots span the ambient module. -/
public theorem typeG2RootPairing_exists_of_simpleRoots_span
    (α₁ α₂ : Vec 2) {N : Type*} [AddCommGroup N] [Module ℝ N]
    (p : Vec 2 →ₗ[ℝ] N →ₗ[ℝ] ℝ) [p.IsPerfPair]
    (coroot : typeG2Roots α₁ α₂ ↪ N)
    (hp : ∀ r, p (typeG2RootEmbedding α₁ α₂ r) (coroot r) = 2)
    (hs : ∀ r, Set.MapsTo
      (Module.preReflection (typeG2RootEmbedding α₁ α₂ r)
        (p.flip (coroot r)))
      (Set.range (typeG2RootEmbedding α₁ α₂))
      (Set.range (typeG2RootEmbedding α₁ α₂)))
    (hspan : Submodule.span ℝ ({α₁, α₂} : Set (Vec 2)) = ⊤) :
    ∃ P : RootPairing (typeG2Roots α₁ α₂) ℝ (Vec 2) N,
      P.root = typeG2RootEmbedding α₁ α₂ ∧ P.coroot = coroot :=
  typeG2RootPairing_exists α₁ α₂ p coroot hp hs
    (typeG2RootEmbedding_span_eq_top_of_simpleRoots α₁ α₂ hspan)

end StandardRootSystem

end Theory.AlgebraicGroup
