module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.Models
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Theory.Representation.SL3.BinaryFieldDescent
public import Theory.Representation.SL3.BinaryFieldDescent.Fields
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
public import Theory.Representation.SL3FourNaturalDual.GraphSeparation

/-!
# The small binary irreducible representations of SL₃(4)

Every irreducible binary representation of dimension at most twelve on which
z² + z + 1 vanishes is equivalent to the concrete natural or dual action.
The proof extends the actual Schur-field representation to its algebraic
closure. The exact word-rotation period forces the Schur degree to divide two.
The central field makes binary dimension even, and the sixteen tensor words
then leave a single natural or dual factor and Schur degree two. A compatible
isomorphism of the Schur field with F₄ descends the actual equivalence to F₂.

Each candidate is irreducible: any irreducible submodule has dimension six
by this catalogue and hence is the whole candidate. Two root displacements
separate the natural and dual binary actions. No faithfulness, absolute
irreducibility or Schur-field size is assumed for the input representation.

Source context: James (1973), Lemma 8.3, cited in Aschbacher–Smith H.12.1(1),
printed pp.393–394. The tensor-word and descent ingredients are GLS III,
2.8.6, Remark 2.8.8 and 2.8.10(c). The descent construction specializes the
existing proof in ChapterG/Section09/DefiningCharacteristic/
LinearThreeRecognition/FieldDescent.lean without importing that CFSG layer.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct MonoidAlgebra
namespace Representation.SL3FourLocalCatalogue
open Representation.SL3.BinaryDefiningFactors
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  (σ : Representation (ZMod 2) SL U) [IsIrreducible σ]
private abbrev SchurField := Module.End (ZMod 2)[SL] σ.asModule
private abbrev SplittingField := AlgebraicClosure (SchurField σ)
private instance schurField_charTwo : CharP (SchurField σ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField σ)).injective 2

private lemma small_word_pattern (w : List Factor) (hlen : w.length = 2)
    (s d r : ℕ) (hd : d = s * wordDegree w) (heven : 2 * r = d)
    (hle : d ≤ 12) (hperiod : ∀ j, w.rotate j = w ↔ s ∣ j) :
    s = 2 ∧ naturalCount w = 1 ∧ adjointCount w = 0 := by
  have hs : s = 1 ∨ s = 2 := (Nat.dvd_prime Nat.prime_two).mp
    ((hperiod 2).mp (hlen ▸ List.rotate_length w))
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  rcases hs with rfl | rfl
  · have hr := (hperiod 1).mpr (one_dvd 1)
    have hab : a = b := (by simpa using hr : b = a ∧ a = b).2
    subst b
    cases a <;> simp [wordDegree, Factor.dimension] at hd <;> omega
  · have hr := (hperiod 1).not.mpr (by decide : ¬ 2 ∣ 1)
    cases a <;> cases b <;>
      simp_all [wordDegree, Factor.dimension, naturalCount, adjointCount]

private lemma absolute_small_natural (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U ≤ 12) :
    Representation.schurDegree 2 σ = 2 ∧
      ∃ ι : F →+* SplittingField σ,
        Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv (natural ι)) ∨
        Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv (natural ι).dual) := by
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra (SplittingField σ) 2
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars (SplittingField σ) σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep (SplittingField σ)
  let ι : F →+* SplittingField σ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := SplittingField σ)).toRingHom
  have hcard : Nat.card F = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_word_equiv ι 2 hcard
    (extendScalars (SplittingField σ) σ.endFieldRep)
  have hp := word_rotate_iff_schurDegree_dvd σ ι w (hw ▸ hcard)
    (fun v hv => wordRep_isIrreducible ι 2 hcard v (hv.trans hw))
    (fun u v hu hv h => (wordRep_equiv_iff ι 2 hcard u v (hu.trans hw) (hv.trans hw)).mp h)
    ⟨e⟩
  have hdim : Module.finrank (ZMod 2) U = Representation.schurDegree 2 σ * wordDegree w := by
    rw [Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  let := fieldModule σ hq
  obtain ⟨hs, hn, ha⟩ := small_word_pattern w hw _ _ _ hdim (field_finrank σ hq) hd hp
  refine ⟨hs, ?_⟩
  obtain ⟨ι', h | h⟩ := wordRep_single_factor ι w hn ha
  · exact ⟨ι', Or.inl (h.map (fun f => e.trans f))⟩
  · exact ⟨ι', Or.inr (h.map (fun f => e.trans f))⟩


variable {K : Type*} [Field K] [Algebra F K]

private def naturalBaseChange :
    (extendScalars K (specialLinearNatural (k := F) 3)).Equiv
      (natural (algebraMap F K)) :=
  .mk (TensorProduct.piScalarRight F K K (Fin 3)) (by
    intro g
    ext v i
    change (TensorProduct.piScalarRight F K K (Fin 3))
      ((1 : K) ⊗ₜ[F] (specialLinearNatural 3 g (Pi.single v 1))) i =
      natural (algebraMap F K) g
        ((TensorProduct.piScalarRight F K K (Fin 3)) ((1 : K) ⊗ₜ[F] (Pi.single v 1))) i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_one]
    change (algebraMap F K) ((g.val.mulVec (Pi.single v 1)) i) =
      ((g.val.map (algebraMap F K)).mulVec
        (fun j => (algebraMap F K) ((Pi.single v 1 : Fin 3 → F) j))) i
    simp [Matrix.mulVec, dotProduct])

private def naturalBinaryEquiv : (constituent .natural).Equiv
    (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)) :=
  .mk (LinearEquiv.refl _ _) (by intro g; rfl)

private def dualBinaryEquiv : (constituent .dual).Equiv
    (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3).dual) :=
  .mk SL3FourNaturalDual.dualCoordinateEquiv (by
    intro g
    apply LinearMap.ext
    intro w
    exact SL3FourNaturalDual.dualCoordinateEquiv_equivariant g w)

open Representation.BinaryFieldDescent
private lemma descend_absolute_natural
    (hs : Representation.schurDegree 2 σ = 2)
    (h : ∃ ι : F →+* SplittingField σ,
      Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv (natural ι)) ∨
      Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv (natural ι).dual)) :
    ∃ a : Constituent, Nonempty (σ.Equiv (constituent a)) := by
  obtain ⟨ι, h⟩ := h
  let : Algebra F (SplittingField σ) := ι.toAlgebra
  have hcard : Nat.card F = Nat.card (SchurField σ) := by
    let : Module.Finite (ZMod 2) (SchurField σ) := Module.Finite.of_finite
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := SchurField σ)
    change Nat.card (SchurField σ) = Nat.card (ZMod 2) ^ Representation.schurDegree 2 σ at he
    rw [he, hs, Nat.card_zmod, Nat.card_eq_fintype_card]
    decide
  obtain ⟨e, he⟩ := FiniteField.exists_compatible_equiv_of_card_eq
    (algebraMap (SchurField σ) (SplittingField σ)) ι hcard
  let := scalarModule σ e
  let : Finite U := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) U)
  let : Module.Finite F U := Module.Finite.of_finite
  let τ := scalarRep σ e
  let eS := scalarExtensionEquiv σ e he
  let eN := naturalBaseChange (K := SplittingField σ)
  rcases h with h | h
  · obtain ⟨ea⟩ := h
    obtain ⟨ed⟩ := equiv_of_extendScalars (K := SplittingField σ) τ
      (specialLinearNatural (k := F) 3) ⟨eS.symm.trans (ea.trans eN.symm)⟩
    refine ⟨.natural, ?_⟩
    have eb := (restrictBinaryEquiv ed).trans naturalBinaryEquiv.symm
    simpa only [τ, restrict_scalarRep] using Nonempty.intro eb
  · obtain ⟨ea⟩ := h
    let eD := (dualBaseChange (K := SplittingField σ)
      (specialLinearNatural (k := F) 3)).trans (dualEquiv eN)
    obtain ⟨ed⟩ := equiv_of_extendScalars (K := SplittingField σ) τ
      (specialLinearNatural (k := F) 3).dual ⟨eS.symm.trans (ea.trans eD.symm)⟩
    refine ⟨.dual, ?_⟩
    have eb := (restrictBinaryEquiv ed).trans dualBinaryEquiv.symm
    simpa only [τ, restrict_scalarRep] using Nonempty.intro eb

/-- Exhaustion of all small irreducible binary modules with nontrivial central
character, retaining an actual representation equivalence. -/
theorem exists_constituent_equiv (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U ≤ 12) :
    ∃ a : Constituent, Nonempty (σ.Equiv (constituent a)) := by
  obtain ⟨hs, h⟩ := absolute_small_natural σ hq hd
  exact descend_absolute_natural σ hs h

/-- Both concrete six-dimensional binary candidate actions are irreducible. -/
theorem constituent_isIrreducible (a : Constituent) : IsIrreducible (constituent a) := by
  obtain ⟨N, hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (constituent a)
  let : IsIrreducible N.toRepresentation := hN
  have hdim : Module.finrank (ZMod 2) N.toSubmodule ≤ 12 :=
    (Submodule.finrank_le N.toSubmodule).trans (by rw [constituent_finrank]; decide)
  obtain ⟨b, ⟨e⟩⟩ := exists_constituent_equiv N.toRepresentation
    (centralQuadratic_subrepresentation _ (constituent_centralQuadratic a) N) hdim
  have ht : N = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.eq_top_of_finrank_eq e.toLinearEquiv.finrank_eq
  have hatom := (Subrepresentation.irreducible_iff_isAtom N).mp hN
  rw [ht] at hatom
  exact isSimpleOrder_iff_isAtom_top.mpr hatom

/-- The two labels give different binary representation isomorphism types. -/
theorem constituent_equiv_iff (a b : Constituent) :
    Nonempty ((constituent a).Equiv (constituent b)) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    cases a <;> cases b
    · rfl
    · exact (SL3FourNaturalDual.no_injective_natural_dual_intertwiner e.toLinearMap
        e.toLinearEquiv.injective (fun g w => LinearMap.congr_fun (e.isIntertwining' g) w)).elim
    · exact (SL3FourNaturalDual.no_injective_natural_dual_intertwiner e.symm.toLinearMap
        e.symm.toLinearEquiv.injective (fun g w => LinearMap.congr_fun (e.symm.isIntertwining' g) w)).elim
    · rfl
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

/-- The small catalogue has no repetitions, with actual binary equivalences. -/
theorem existsUnique_constituent_equiv (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U ≤ 12) :
    ∃! a : Constituent, Nonempty (σ.Equiv (constituent a)) := by
  obtain ⟨a, ⟨e⟩⟩ := exists_constituent_equiv σ hq hd
  refine ⟨a, ⟨e⟩, ?_⟩
  rintro b ⟨f⟩
  exact (constituent_equiv_iff b a).mp ⟨f.symm.trans e⟩

/-- In this dimension range, every irreducible with the central quadratic
relation has binary dimension exactly six. -/
theorem finrank_eq_six_of_irreducible (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U ≤ 12) :
    Module.finrank (ZMod 2) U = 6 := by
  obtain ⟨a, ⟨e⟩⟩ := exists_constituent_equiv σ hq hd
  exact e.toLinearEquiv.finrank_eq.trans constituent_finrank

end Representation.SL3FourLocalCatalogue
