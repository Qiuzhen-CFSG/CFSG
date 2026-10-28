module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.FrobeniusCounts.HermitianDual
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction.ActionLift
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction.SchurTransport
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction.WordConjugation
public import Theory.Representation.IrreducibleTraceEquivalence

/-!
# Symmetric labels from the literal outer Schur-linear involution

The action image is perfect and its genuine central quotient is PSU₃. Its
outer involution lifts to a conjugate-entrywise matrix automorphism of the
original SU₃, even with nontrivial central kernel. The literal Schur-linear
actor intertwines the absolute representation with this pullback. Matrix
conjugation and the original Hermitian Gram pairing identify its character
with that of the word with natural and dual labels exchanged.

Irreducibility and uniqueness in the permitted length-s word catalogue now
force equality of the two lists. Every label is therefore trivial or adjoint.
This proves the symmetric-highest-weight step of GM04, Proposition 4.11,
internal pp.31--32, without any displacement or natural-recognition input.
-/

public section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Representation Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors Representation.BinaryOffender
open Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
open MinimalDegree

section Characters
variable {F K : Type*} [Field F] [Field K] [CharP K 2] [IsAlgClosed K]
  (J : HermitianForm 3 F)

private theorem word_character_hermitian_power (ι : F →+* K) (w : List Factor)
    (s : ℕ) (hc : ∀ x, J.conj x = x ^ (2 ^ s)) (g : J.specialSubgroup) :
    (word J ι w).character g ^ (2 ^ s) = (word J ι (dualWord w)).character g := by
  induction w generalizing ι with
  | nil =>
    change (wordRep ι []).character (specialLinearInclusion J g) ^ (2 ^ s) =
      (wordRep ι []).character (specialLinearInclusion J g)
    simp only [wordRep_character_nil, one_pow]
  | cons a w ih =>
    change (wordRep ι (a :: w)).character (specialLinearInclusion J g) ^ (2 ^ s) =
      (wordRep ι (dualFactor a :: dualWord w)).character (specialLinearInclusion J g)
    rw [wordRep_character_cons, wordRep_character_cons, mul_pow,
      factor_character_unitary_frobenius J ι s hc]
    exact congrArg ((factorRep ι (dualFactor a)).character (specialLinearInclusion J g) * ·)
      (ih ((frobenius K 2).comp ι))

/-- The Gram pairing identifies coefficient Hermitian conjugation with
exchanging natural and dual labels in the entire actual tensor word. -/
theorem word_character_hermitian_dual (ι : F →+* K) (w : List Factor)
    (s : ℕ) (hc : ∀ x, J.conj x = x ^ (2 ^ s)) (g : J.specialSubgroup) :
    (word J (ι.comp J.conj.toRingHom) w).character g =
      (word J ι (dualWord w)).character g := by
  have hem : (iterateFrobeniusEquiv K 2 s : K →+* K).comp ι =
      ι.comp J.conj.toRingHom := by
    ext x
    change (ι x) ^ (2 ^ s) = ι (J.conj x)
    rw [hc, map_pow]
  have hf := wordRep_character_comp (iterateFrobeniusEquiv K 2 s) ι w
    (specialLinearInclusion J g)
  rw [hem] at hf
  exact hf.trans (word_character_hermitian_power J ι w s hc g)

private theorem word_character_matrix_lift (ι : F →+* K) (w : List Factor)
    (β : MulAut J.specialSubgroup) (D : Matrix.GeneralLinearGroup (Fin 3) F)
    (hm : ∀ g, (β g).val =
      D * Matrix.GeneralLinearGroup.map J.conj.toRingHom g.val * D⁻¹)
    (g : J.specialSubgroup) :
    (word J ι w).character (β g) =
      (word J (ι.comp J.conj.toRingHom) w).character g := by
  apply word_character_semilinear ι w (specialLinearInclusion J)
    ((specialLinearInclusion J).comp β.toMonoidHom) J.conj.toRingHom D _ g
  intro x
  have incl (x : J.specialSubgroup) :
      Matrix.SpecialLinearGroup.toGL (specialLinearInclusion J x) = x.val := Units.ext rfl
  have hmap : Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map J.conj.toRingHom (specialLinearInclusion J x)) =
        Matrix.GeneralLinearGroup.map J.conj.toRingHom x.val := Units.ext rfl
  change D * Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map J.conj.toRingHom (specialLinearInclusion J x)) =
    Matrix.SpecialLinearGroup.toGL (specialLinearInclusion J (β x)) * D
  rw [incl, hmap, hm]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end Characters

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
  (hk : σ.ker ≤ Subgroup.center J.specialSubgroup)

include hs hcard hconj hk

/-- The actual outer Schur-linear involution forces symmetric labels.
The only catalogue assumptions are irreducibility and uniqueness of words;
no graph stability or displacement estimate is assumed. -/
theorem outerLabelSymmetry_of_catalogue
    (hirr : ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
      IsIrreducible (word J ι w))
    (hunique : ∀ (ι : F →+* Closure σ) (u v : List Factor),
      u.length = s → v.length = s →
      Nonempty ((word J ι u).Equiv (word J ι v)) → u = v) :
    OuterLabelSymmetry J σ s := by
  intro ι w hw he t ht hl ho
  obtain ⟨E⟩ := he
  obtain ⟨β, D, hβ, hm⟩ := outer_normalizer_matrix_lift J hs hcard hconj σ hk t ht ho
  have hchar : (word J ι w).character = (word J ι (dualWord w)).character := by
    funext g
    calc
      (word J ι w).character g = (absoluteRep σ).character g :=
        (congrFun (char_iso E) g).symm
      _ = (absoluteRep σ).character (β g) :=
        (absolute_character_lift σ t ht hl β hβ g).symm
      _ = (word J ι w).character (β g) := congrFun (char_iso E) (β g)
      _ = (word J (ι.comp J.conj.toRingHom) w).character g :=
        word_character_matrix_lift J ι w β D hm g
      _ = (word J ι (dualWord w)).character g :=
        word_character_hermitian_dual J ι w s hconj g
  let : IsIrreducible (word J ι w) := hirr ι w hw
  let : IsIrreducible (word J ι (dualWord w)) := hirr ι _ (by simpa using hw)
  have hd := hunique ι w (dualWord w) hw (by simpa using hw)
    ((character_eq_iff_equiv_of_irreducible _ _).mp hchar)
  have hmap : w.map dualFactor = w.map id := by simpa only [List.map_id, dualWord] using hd.symm
  apply List.countP_eq_zero.mpr
  intro a ha
  have hfix := List.map_inj_left.mp hmap a ha
  cases a <;> simp [dualFactor] at hfix ⊢

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
