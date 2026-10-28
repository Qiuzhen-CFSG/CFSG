module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.WordBounds
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.TensorWords
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.FrobeniusCounts.TwistedRotation
public import Theory.Representation.EndFieldFrobenius

/-!
# Twisted Frobenius counts for the actual binary SU₃ Schur model

For an actual Schur extension equivalent to a length-s unitary tensor word,
`periodCounts_of_schur_word` proves the two orbit-count alternatives consumed by
`single_factor_of_periodCounts`. Its only catalogue inputs are irreducibility
and separation of length-s words. The final nontriviality argument has exactly
the form of the `hperiod` input to `source_naturalModel_of_schur_word`.

The proof identifies the Schur degree with the exact rotation period of the
folded word. Hermitian duality supplies the graph twist, and repeated-block
counts give the natural or adjoint alternative. The field-cardinality and
minimal-degree bounds are unnecessary for this step; the source application
uses them in the subsequent numerical and descent arguments.

Source: GLS III, Remark 2.8.8; Guralnick--Malle, §3.1, internal p.12.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
open scoped MonoidAlgebra TensorProduct
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
variable {F K V : Type*} [Field F] [Field K] [CharP K 2] [IsAlgClosed K]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
  [Algebra (Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) K]

omit [IsAlgClosed K] in
/-- Nontriviality of the original binary action survives Schur scalar extension,
so its actual tensor word has a natural, dual, or adjoint factor. -/
theorem counts_pos_of_schur_word (ι : F →+* K) (w : List Factor)
    (hne : ∃ g, σ g ≠ 1)
    (hmodel : Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w))) :
    0 < naturalCount w + adjointCount w := by
  by_contra h
  have hn : naturalCount w = 0 := by omega
  have ha : adjointCount w = 0 := by omega
  obtain ⟨g, hg⟩ := hne
  obtain ⟨E⟩ := hmodel
  have hwg : word J ι w g = 1 :=
    wordRep_eq_one_of_counts_zero ι w hn ha (specialLinearInclusion J g)
  have hext : extendScalars K σ.endFieldRep g = 1 := by
    apply LinearMap.ext
    intro v
    apply E.toLinearEquiv.injective
    have ht := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v
    simpa only [Representation.Equiv.toLinearEquiv_apply, hwg, Module.End.one_apply] using ht
  have he : σ.endFieldRep g = 1 := by
    apply LinearMap.baseChangeHom_injective
      (R := Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) (S := K)
      (M := σ.asModule) (N := σ.asModule)
    change (σ.endFieldRep g).baseChange K = (1 : Module.End _ σ.asModule).baseChange K
    simpa only [extendScalars_apply, LinearMap.baseChange_one] using hext
  apply hg
  ext v
  have h := LinearMap.congr_fun he (σ.asModuleEquiv.symm v)
  have h' := congrArg σ.asModuleEquiv h
  simpa only [endFieldRep_apply', LinearEquiv.apply_symm_apply, Module.End.one_apply] using h'

/-- Transfer the exact Schur Frobenius period to a folded word once its
coefficient-transport criterion has been proved. -/
theorem folded_rotation_iff_schurDegree_dvd_of_transport
    (ι : F →+* K) (w : List Factor)
    (hirr : IsIrreducible (word J ι w))
    (hmodel : Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)))
    (htransport : ∀ r : ℕ,
      Nonempty ((word J ι w).Equiv (frobeniusConjugate 2 r (word J ι w))) ↔
        (foldedWord w).rotate r = foldedWord w)
    (r : ℕ) :
    (foldedWord w).rotate r = foldedWord w ↔ schurDegree 2 σ ∣ r := by
  obtain ⟨E⟩ := hmodel
  let : IsIrreducible (word J ι w) := hirr
  let : IsIrreducible (frobeniusConjugate 2 r (word J ι w)) :=
    frobeniusConjugate_isIrreducible 2 r _
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars K σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep K
  let : IsIrreducible (frobeniusConjugate 2 r (extendScalars K σ.endFieldRep)) :=
    frobeniusConjugate_isIrreducible 2 r _
  rw [← htransport r, ← endFieldRep_frobenius_equiv_iff 2 σ K r,
    ← character_eq_iff_equiv_of_irreducible,
    ← character_eq_iff_equiv_of_irreducible]
  simp only [funext_iff, character_frobeniusConjugate, char_iso E]

/-- Apply repeated-block counts to the actual nontrivial binary Schur model.
The final theorem below supplies the transport criterion from Hermitian duality. -/
theorem periodCounts_of_schur_word_transport {s : ℕ} (hs : 0 < s)
    (ι : F →+* K) (w : List Factor) (hw : w.length = s)
    (hne : ∃ g, σ g ≠ 1)
    (hirr : IsIrreducible (word J ι w))
    (hmodel : Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)))
    (htransport : ∀ r : ℕ,
      Nonempty ((word J ι w).Equiv (frobeniusConjugate 2 r (word J ι w))) ↔
        (foldedWord w).rotate r = foldedWord w) :
    PeriodCounts s (schurDegree 2 σ) w := by
  have hp := folded_rotation_iff_schurDegree_dvd_of_transport J σ ι w hirr hmodel htransport
  have hd : schurDegree 2 σ ∣ 2 * s := by
    apply (hp (2 * s)).mp
    simpa only [foldedWord_length, hw] using List.rotate_length (foldedWord w)
  exact periodCounts_of_folded_rotation s (schurDegree 2 σ) w hs hw hd
    (counts_pos_of_schur_word J σ ι w hne hmodel)
    (fun r hr => (hp r).mp hr) ((hp _).mpr (dvd_refl _))


/-- Twisted Frobenius orbit counts for an actual nontrivial binary SU₃ Schur
model. Only irreducibility and separation of the length-s word catalogue remain
as explicit catalogue assumptions. No faithfulness, field-period, degree bound,
or natural-module identification is assumed. -/
theorem periodCounts_of_schur_word {s : ℕ} (hs : 2 ≤ s)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (w : List Factor) (hw : w.length = s)
    (hirr : ∀ v : List Factor, v.length = s → IsIrreducible (word J ι v))
    (hunique : ∀ u v : List Factor, u.length = s → v.length = s →
      Nonempty ((word J ι u).Equiv (word J ι v)) → u = v)
    (hmodel : Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)))
    (hne : ∃ g, σ g ≠ 1) : PeriodCounts s (schurDegree 2 σ) w := by
  apply periodCounts_of_schur_word_transport J σ (by omega) ι w hw hne
    (hirr w hw) hmodel
  exact word_frobenius_equiv_iff_folded_rotation J ι w
    (fun x => by simpa only [hw] using hconj x)
    (fun v hv => hirr v (hv.trans hw))
    (fun u v hu hv => hunique u v (hu.trans hw) (hv.trans hw))

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
