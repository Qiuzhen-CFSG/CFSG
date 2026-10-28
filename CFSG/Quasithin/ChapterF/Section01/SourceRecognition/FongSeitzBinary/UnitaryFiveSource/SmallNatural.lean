module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalDescent
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.SmallClasses

/-!
# Natural coordinates for the small binary unitary actor

A nontrivial irreducible binary action of the full SU₃(2), of degree at most
six, is its natural three-space over the quadratic field. The four length-one
words are simple and separated by the actual highest-line torus characters
and dimensions. The small odd-order class bound proves their exhaustion.
Twisted Frobenius periods then force one natural or dual factor with Schur
field of order four, and the existing descent constructs an actual
intertwining linear equivalence.

Combining this with the existing larger-field class bound gives coordinates
in every positive binary degree, preserving the original actor marking.

The fixed-line, orbit-span and separation arguments below adapt the existing
`MinimalDegree/Catalogue/RestrictedWords/{StandardGeometry,TorusSeparation}`
proofs to positive degree. Their interpolation inputs already include degree
one. No perfectness, faithfulness or natural-coordinate witness is assumed.
This closes the small-field realization step in Fong--Seitz I (4D), (6A)(c),
and II (8C), pp.203--204; source application is in `NaturalAllFields`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MonoidAlgebra TensorProduct
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External Representation
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity
open Representation.SU3.BinaryDefiningWords.WeightSeparation
open Matrix.PSL3Even.UnipotentGeometry FixedLine
open CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
open CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
open CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree.RestrictedWords
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource.SmallNatural
variable {F K : Type*} [Field F] [Finite F] [Field K] [CharP K 2]

/-- Every upper-unitary fixed vector belongs to the concrete highest-tensor line. -/
private theorem word_fixed_mem_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) (v : WordSpace K w)
    (hv : ∀ z : hermitianUnipotentCoord J,
      word J ι w (hermitianUnipotentSU J hJ z) v = v) :
    v ∈ Submodule.span K {wordSeed K w} := by
  let c := MvPolynomial.eval (0 : Fin 3 → K) (wordPolynomial K w v)
  have he : wordPolynomial K w (v - c • wordSeed K w) = 0 := by
    apply wordPolynomial_eq_zero_of_unitary_eval J hJ s (by omega) hcard hconj ι w hw
    intro z
    rw [map_sub, map_smul, wordPolynomial_seed, map_sub, MvPolynomial.smul_eval,
      map_one, mul_one, wordPolynomial_eval, ← upper_inclusion J hJ]
    change MvPolynomial.eval (0 : Fin 3 → K)
      (wordPolynomial K w (word J ι w (hermitianUnipotentSU J hJ z) v)) - c = 0
    rw [hv z]
    exact sub_self c
  have hz : v - c • wordSeed K w = 0 :=
    wordPolynomial_injective K w (he.trans (map_zero _).symm)
  exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hz).symm⟩

/-- Exact equality of the upper fixed space and the seed line. -/
private theorem word_fixed_iff_mem_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) (v : WordSpace K w) :
    (∀ z : hermitianUnipotentCoord J,
      word J ι w (hermitianUnipotentSU J hJ z) v = v) ↔
      v ∈ Submodule.span K {wordSeed K w} := by
  refine ⟨word_fixed_mem_span_standard J hJ s hs hcard hconj ι w hw v, ?_⟩
  intro hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  intro z
  rw [map_smul, word_seed_fixed]

private theorem wordPairing_injective_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) :
    Function.Injective (wordPairing K w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply wordPolynomial_injective K w
  rw [map_zero]
  apply wordPolynomial_eq_zero_of_unitary_eval J hJ s hs hcard hconj ι w hw
  intro z
  rw [wordPolynomial_eval_pairing, hv]
  rfl

/-- The actual lower-unitary orbit already spans the word carrier. -/
private theorem wordSeed_lower_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) :
    Submodule.span K (Set.range fun z : hermitianUnipotentCoord J =>
      word J ι w (lowerUnitary J hJ z) (wordSeed K w)) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply bot_unique
  intro f hf
  have hsurj : Function.Surjective (wordPairing K w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp
        (wordPairing_injective_standard J hJ s (by omega) hcard hconj ι w hw)
  obtain ⟨v, rfl⟩ := hsurj f
  have hv : v = 0 := by
    apply wordPolynomial_injective K w
    rw [map_zero]
    apply wordPolynomial_eq_zero_of_unitary_eval J hJ s (by omega) hcard hconj ι w hw
    intro z
    rw [wordPolynomial_eval_pairing, ← lower_inclusion J hJ]
    exact (Submodule.mem_dualAnnihilator _).mp hf _ (Submodule.subset_span ⟨z, rfl⟩)
  simp [hv]

/-- The full special-unitary orbit of the concrete highest tensor spans the word. -/
private theorem wordSeed_orbit_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) :
    Submodule.span K (Set.range fun g : J.specialSubgroup =>
      word J ι w g (wordSeed K w)) = ⊤ := by
  apply top_unique
  rw [← wordSeed_lower_span_standard J hJ s hs hcard hconj ι w hw]
  apply Submodule.span_mono
  rintro _ ⟨z, rfl⟩
  exact ⟨lowerUnitary J hJ z, rfl⟩

/-- Every source-restricted standard-form word is irreducible, by the proved
fixed-line and spanning results for its literal unitary action. -/
private theorem word_isIrreducible_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) : IsIrreducible (word J ι w) := by
  let : CharP F 2 := ι.charP ι.injective 2
  exact word_isIrreducible_of_fixedLine_and_span J hJ ι w
    (word_fixed_mem_span_standard J hJ s hs hcard hconj ι w hw)
    (wordSeed_orbit_span_standard J hJ s hs hcard hconj ι w hw)

/-- Upper fixed-line geometry suffices for separation of the actual standard-form words. -/
private theorem word_equiv_iff_of_fixedLine
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hfixed : ∀ u : List Factor, u.length = s → ∀ x : WordSpace K u,
      (∀ z : hermitianUnipotentCoord J,
        word J ι u (hermitianUnipotentSU J hJ z) x = x) →
      x ∈ Submodule.span K {wordSeed K u})
    (v w : List Factor) (hv : v.length = s) (hw : w.length = s) :
    Nonempty ((word J ι v).Equiv (word J ι w)) ↔ v = w := by
  constructor
  · rintro ⟨e⟩
    have commute (g : J.specialSubgroup) (x : WordSpace K v) :
        e (word J ι v g x) = word J ι w g (e x) :=
      LinearMap.congr_fun (e.isIntertwining' g) x
    have hmem := hfixed w hw (e (wordSeed K v)) (fun z => by
      rw [← commute, word_seed_fixed])
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_smul] at hc
      exact wordSeed_ne_zero K v (e.toLinearEquiv.map_eq_zero_iff.mp hc.symm)
    have hchars (k : Fˣ) :
        (ι (k : F)) ^ exponent (2 ^ s) v = (ι (k : F)) ^ exponent (2 ^ s) w := by
      have h := commute (hermitianTorusSU J hJ k⁻¹) (wordSeed K v)
      rw [TorusSeparation.wordSeed_torus J hJ ι (2 ^ s) hconj,
        map_smul, ← hc, map_smul,
        TorusSeparation.wordSeed_torus J hJ ι (2 ^ s) hconj] at h
      simp only [Units.val_inv_eq_inv_val, inv_inv, smul_smul] at h
      have hh := smul_left_injective K (wordSeed_ne_zero K w) h
      apply mul_right_cancel₀ hc0
      simpa only [mul_comm c] using hh
    have hd : wordDegree v = wordDegree w := by
      simpa only [finrank_wordSpace] using e.toLinearEquiv.finrank_eq
    apply eq_of_unit_powers_and_degree s (by omega) hcard v w hv hw _ hd
    intro k
    apply Units.ext
    apply ι.injective
    simpa only [Units.val_pow_eq_pow_val, map_pow] using hchars k
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩


/-- Natural unitary recognition in every positive binary degree, including
degree one, preserving the original full special-group marking. -/
theorem natural_equiv_of_finrank_le [Algebra (ZMod 2) F]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
    {s : ℕ} (hs : 0 < s)
    (hcard : Nat.card F = (2^s)^2) (hconj : ∀ x, J.conj x = x^(2^s))
    (hne : ∃ g, σ g ≠ 1) (hd : Module.finrank (ZMod 2) V ≤ 6*s) :
    Nonempty (σ.Equiv
      (restrictScalars (k := ZMod 2) (natural J (RingHom.id F)))) := by
  let E := Module.End (ZMod 2)[J.specialSubgroup] σ.asModule
  let K' := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP K' 2 := charP_of_injective_algebraMap (algebraMap E K').injective 2
  let : Algebra (ZMod 2) K' := ZMod.algebra K' 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let ι : F →+* K' := (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := K')).toRingHom
  have hirr (w : List Factor) (hw : w.length = s) : IsIrreducible (word J ι w) :=
    word_isIrreducible_standard J hJ s hs hcard hconj ι w hw
  have hsep (u v : List Factor) (hu : u.length = s) (hv : v.length = s) :
      Nonempty ((word J ι u).Equiv (word J ι v)) → u = v :=
    (word_equiv_iff_of_fixedLine J hJ s hs hcard hconj ι
      (word_fixed_mem_span_standard J hJ s hs hcard hconj ι) u v hu hv).mp
  have hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F := by
    by_cases hs2 : 2 ≤ s
    · exact Theory.SpecificGroups.SU3.BinaryPRegularClasses.card_pRegularConjClasses_le
        J s hs2 hcard hconj
    have hs1 : s = 1 := by omega
    subst s
    exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource.SmallClasses.card_pRegularConjClasses_le J hcard hconj hJ
  obtain ⟨w,hw,hmodel⟩ := exists_schur_word_model_of_simple_family_and_class_bound
    J σ s ι hcard hirr hsep hclasses
  have hperiod : PeriodCounts s (schurDegree 2 σ) w := by
    apply periodCounts_of_schur_word_transport J σ hs ι w hw hne (hirr w hw) hmodel
    exact word_frobenius_equiv_iff_folded_rotation J ι w
      (fun x => by simpa only [hw] using hconj x)
      (fun v hv => hirr v (hv.trans hw))
      (fun u v hu hv => hsep u v (hu.trans hw) (hv.trans hw))
  obtain ⟨he,hm⟩ := schur_word_single_factor J σ ι w hmodel hperiod hd
  exact NaturalDescent.natural_equiv_of_absolute_natural J σ hcard he hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource.SmallNatural
