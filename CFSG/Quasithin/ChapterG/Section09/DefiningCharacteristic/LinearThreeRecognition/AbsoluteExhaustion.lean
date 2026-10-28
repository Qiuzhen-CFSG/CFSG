module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.OrbitDegrees
public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns
public import Theory.Representation.EndFieldFrobenius

/-!
# Exhaustive absolute models for binary SL₃ representations

The concrete tensor-word catalogue classifies the scalar extension of the
actual Schur-field representation. Its exact coefficient Frobenius period
identifies the repeated-block length with the Schur degree. Faithful scalar
extension shows that a nontrivial binary action has a nontrivial tensor factor.
The dimension tower and numerical orbit gap then leave just a single natural
or dual factor, a doubled block of that form, or dimension at least 8n.

The exceptional patterns give actual representation equivalences to the
natural action or the half-field twisted tensor, with coefficient embeddings
and duality as specified by `HasAbsoluteNaturalModel` and
`HasAbsoluteTwistedModel`. The final `absolute_model_trichotomy` assumes only
irreducibility, nontrivial action, and the stated finite-field hypotheses;
classification, period and model-equivalence premises are all discharged.

Source: GLS III 2.8.6, 2.8.8, 2.8.10(c); Aschbacher--Smith G.9.3,
printed pp.354,356--357. This supplies absolute exhaustion for the SL₃ branch;
descent to binary models and the actor-rank bounds belong to its consumers.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open Representation
open scoped MatrixGroups TensorProduct MonoidAlgebra

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion

open Representation.SL3.BinaryDefiningFactors

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]

/-- The actual commuting endomorphism field has characteristic two. -/
instance schurField_charTwo : CharP (SchurField ρ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2

/-- Positivity is intrinsic to the actual Schur field. -/
theorem schurDegree_pos : 0 < schurDegree ρ :=
  Representation.schurDegree_pos 2 ρ

/-- An actual word equivalence determines the binary dimension. -/
theorem finrank_of_word_model (ι : F →+* SplittingField ρ) (w : List Factor)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι w))) :
    Module.finrank (ZMod 2) V = schurDegree ρ * wordDegree w := by
  obtain ⟨φ⟩ := hmodel
  calc
    Module.finrank (ZMod 2) V = schurDegree ρ *
        Module.finrank (SplittingField ρ)
          (SplittingField ρ ⊗[SchurField ρ] ρ.asModule) :=
      Representation.finrank_eq_schurDegree_mul 2 ρ (SplittingField ρ)
    _ = schurDegree ρ * wordDegree w := by
      rw [φ.toLinearEquiv.finrank_eq, finrank_wordSpace]

private theorem eq_one_of_equiv {K G M N : Type*} [Field K] [Monoid G]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {σ : Representation K G M} {τ : Representation K G N} (φ : σ.Equiv τ)
    (g : G) (h : τ g = 1) : σ g = 1 := by
  ext v
  apply φ.toLinearEquiv.injective
  change φ (σ g v) = φ v
  have hc := Representation.IntertwiningMap.isIntertwining σ τ φ.toIntertwiningMap g v
  rw [h] at hc
  exact hc

private theorem eq_one_of_schur_scalar_extension (g : SL(3,F))
    (h : extendScalars (SplittingField ρ) ρ.endFieldRep g = 1) : ρ g = 1 := by
  have he : ρ.endFieldRep g = 1 := by
    ext v
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := SchurField ρ) (B := SplittingField ρ) ρ.asModule)
    exact congrArg (fun f : Module.End (SplittingField ρ)
      (SplittingField ρ ⊗[SchurField ρ] ρ.asModule) => f (1 ⊗ₜ[SchurField ρ] v)) h
  ext v
  have hh := congrArg (fun f : Module.End (SchurField ρ) ρ.asModule =>
    ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) he
  simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply, Module.End.one_apply] using hh

/-- A nontrivial binary action has a nontrivial tensor factor. -/
theorem counts_pos_of_word_model (hact : ∃ g, ρ g ≠ 1)
    (ι : F →+* SplittingField ρ) (w : List Factor)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι w))) :
    0 < naturalCount w + adjointCount w := by
  obtain ⟨φ⟩ := hmodel
  obtain ⟨g, hg⟩ := hact
  by_contra h
  have ha : naturalCount w = 0 := by omega
  have hb : adjointCount w = 0 := by omega
  exact hg (eq_one_of_schur_scalar_extension ρ g
    (eq_one_of_equiv φ g (wordRep_eq_one_of_counts_zero ι w ha hb g)))

/-- The binary dimension formula for an actual repeated-block model. -/
theorem finrank_of_repeated_word_model (ι : F →+* SplittingField ρ)
    (w : List Factor) (t : ℕ)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι (List.replicate t w).flatten))) :
    Module.finrank (ZMod 2) V =
      schurDegree ρ * (3 ^ naturalCount w * 8 ^ adjointCount w) ^ t := by
  rw [finrank_of_word_model ρ ι _ hmodel, wordDegree_repeat]

/-- A block underlying a nontrivial binary action has a nontrivial factor. -/
theorem counts_pos_of_repeated_word_model (hact : ∃ g, ρ g ≠ 1)
    (ι : F →+* SplittingField ρ) (w : List Factor) (t : ℕ)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι (List.replicate t w).flatten))) :
    0 < naturalCount w + adjointCount w := by
  have h := counts_pos_of_word_model ρ hact ι _ hmodel
  rw [naturalCount_repeat, adjointCount_repeat] at h
  by_contra hc
  have ha : naturalCount w = 0 := by omega
  have hb : adjointCount w = 0 := by omega
  simp [ha, hb] at h

/-- Numerical reduction retaining the exceptional word patterns. This does not
assert their equivalence to the published absolute natural or tensor models. -/
theorem degree_alternatives_of_repeated_word_model (hact : ∃ g, ρ g ≠ 1)
    (ι : F →+* SplittingField ρ) (w : List Factor) (n t : ℕ)
    (ht : 0 < t)
    (hn : n = schurDegree ρ * t)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι (List.replicate t w).flatten))) :
    (naturalCount w = 1 ∧ adjointCount w = 0 ∧ t = 1 ∧
      schurDegree ρ = n ∧ Module.finrank (ZMod 2) V = 3 * n) ∨
    (naturalCount w = 1 ∧ adjointCount w = 0 ∧ t = 2 ∧
      n = 2 * schurDegree ρ ∧ Module.finrank (ZMod 2) V = 9 * schurDegree ρ) ∨
    8 * n ≤ Module.finrank (ZMod 2) V := by
  have hd := finrank_of_repeated_word_model ρ ι w t hmodel
  have hab := counts_pos_of_repeated_word_model ρ hact ι w t hmodel
  rcases orbit_degree_gap (s := schurDegree ρ) ht hab with
    ⟨ha, hb, ht1⟩ | ⟨ha, hb, ht2⟩ | hgap
  · left
    refine ⟨ha, hb, ht1, ?_, ?_⟩
    · simpa [ht1] using hn.symm
    · simpa [ha, hb, ht1, hn, Nat.mul_comm] using hd
  · right; left
    refine ⟨ha, hb, ht2, ?_, ?_⟩
    · simpa [ht2, Nat.mul_comm] using hn
    · simpa [ha, hb, ht2, Nat.mul_comm] using hd
  · right; right
    simpa [← hn, ← hd] using hgap

variable [Finite F] [CharP F 2]

/-- Every binary irreducible has an actual tensor-word model consisting of
positive copies of a block whose length is its Schur degree. The word
classification and exact Frobenius period are proved, not assumed. -/
theorem exists_repeated_word_model (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = 2 ^ n) :
    ∃ (ι : F →+* SplittingField ρ) (t : ℕ) (b : List Factor),
      0 < t ∧ b.length = schurDegree ρ ∧ n = schurDegree ρ * t ∧
      Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
        (wordRep ι (List.replicate t b).flatten)) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Algebra (ZMod 2) (SplittingField ρ) := ZMod.algebra (SplittingField ρ) 2
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars (SplittingField ρ) ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep (SplittingField ρ)
  let ι : F →+* SplittingField ρ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := SplittingField ρ)).toRingHom
  obtain ⟨w, hw, he⟩ := exists_word_equiv ι n hcard
    (extendScalars (SplittingField ρ) ρ.endFieldRep)
  obtain ⟨t, b, ht, hb, hn, hrep⟩ :=
    exists_repeated_block_of_word_model ρ ι w n hn hw hcard
      (wordRep_isIrreducible ι n hcard)
      (fun u v hu hv h => (wordRep_equiv_iff ι n hcard u v hu hv).mp h) he
  exact ⟨ι, t, b, ht, hb, hn, hrep ▸ he⟩

/-- Exhaustive absolute SL₃ recognition in characteristic two. Apart from the
natural and half-field tensor models (including their duals), every nontrivial
binary irreducible has dimension at least eight times the field exponent. -/
theorem absolute_model_trichotomy (hact : ∃ g, ρ g ≠ 1)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = 2 ^ n) :
    0 < schurDegree ρ ∧
      ((schurDegree ρ = n ∧ Module.finrank (ZMod 2) V = 3 * n ∧
          HasAbsoluteNaturalModel ρ) ∨
        (n = 2 * schurDegree ρ ∧ Module.finrank (ZMod 2) V = 9 * schurDegree ρ ∧
          HasAbsoluteTwistedModel ρ (schurDegree ρ)) ∨
        8 * n ≤ Module.finrank (ZMod 2) V) := by
  refine ⟨schurDegree_pos ρ, ?_⟩
  obtain ⟨ι, t, b, ht, hb, hnt, he⟩ := exists_repeated_word_model ρ n hn hcard
  rcases degree_alternatives_of_repeated_word_model ρ hact ι b n t ht hnt he with
    ⟨ha, hadj, ht1, hs, hd⟩ | ⟨ha, hadj, ht2, hs, hd⟩ | hgap
  · left
    refine ⟨hs, hd, ?_⟩
    subst t
    rw [show (List.replicate 1 b).flatten = b by simp] at he
    obtain ⟨e⟩ := he
    obtain ⟨ι', hnatural | hdual⟩ := wordRep_single_factor ι b ha hadj
    · exact ⟨ι', Or.inl (hnatural.map (fun f => e.trans f))⟩
    · exact ⟨ι', Or.inr (hdual.map (fun f => e.trans f))⟩
  · right; left
    refine ⟨hs, hd, ?_⟩
    subst t
    obtain ⟨e⟩ := he
    obtain ⟨σ, hσ, ι', hnatural | hdual⟩ := wordRep_double_single_factor ι b ha hadj
    · exact ⟨σ, by simpa only [hb] using hσ, ι',
        Or.inl (hnatural.map (fun f => e.trans f))⟩
    · exact ⟨σ, by simpa only [hb] using hσ, ι',
        Or.inr (hdual.map (fun f => e.trans f))⟩
  · exact Or.inr (Or.inr hgap)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
