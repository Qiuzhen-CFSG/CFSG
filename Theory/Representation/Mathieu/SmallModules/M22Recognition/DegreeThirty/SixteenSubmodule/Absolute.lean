module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.Models

/-!
# The exact Schur orbit of a sixteen-dimensional point constituent

The proved SL₃ tensor catalogue, over the algebraic closure of the actual
commuting field, forces Schur degree two and exactly one adjoint factor.
The two possible words differ by Frobenius. This identifies an actual
representation after scalar extension, not merely its degree or a family tag.
The final theorem applies the calculation to the literal point submodule.

Source: GLS III, 2.8.6, Remark 2.8.8 and 2.8.10(c); the consumer is the
M22 degree gap used in Guralnick–Malle I, Proposition 5.1, pp.15–16.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
open scoped MonoidAlgebra
open Representation.SL3.BinaryDefiningFactors
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

private lemma sixteen_word (w : List Factor) (hlen : w.length = 2)
    (s : ℕ) (hd : 16 = s * wordDegree w)
    (hperiod : ∀ j, w.rotate j = w ↔ s ∣ j) :
    s = 2 ∧ (w = [.adjoint, .trivial] ∨ w = [.trivial, .adjoint]) := by
  have hs : s = 1 ∨ s = 2 := (Nat.dvd_prime Nat.prime_two).mp
    ((hperiod 2).mp (hlen ▸ List.rotate_length w))
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  rcases hs with rfl | rfl
  · have hr := (hperiod 1).mpr (one_dvd 1)
    have hab : a = b := (by simpa using hr : b = a ∧ a = b).2
    subst b
    cases a <;> simp [wordDegree, Factor.dimension] at hd
  · cases a <;> cases b <;> simp_all [wordDegree, Factor.dimension]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (τ : Representation (ZMod 2) Matrix.PSL3Four.SL W) [τ.IsIrreducible]

/-- Algebraic closure of the actual commuting endomorphism field. -/
abbrev SplittingField := AlgebraicClosure (Module.End (ZMod 2)[Matrix.PSL3Four.SL] τ.asModule)

instance endField_charTwo :
    CharP (Module.End (ZMod 2)[Matrix.PSL3Four.SL] τ.asModule) 2 :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (Module.End (ZMod 2)[Matrix.PSL3Four.SL] τ.asModule)).injective 2

/-- Degree sixteen gives the genuine adjoint Frobenius orbit and Schur degree
two. No absolute irreducibility over the binary field is assumed. -/
theorem absolute_adjoint_orbit (hd : Module.finrank (ZMod 2) W = 16) :
    Representation.schurDegree 2 τ = 2 ∧
      ∃ (ι : Matrix.PSL3Four.F →+* SplittingField τ) (w : List Factor),
        (w = [.adjoint, .trivial] ∨ w = [.trivial, .adjoint]) ∧
        Nonempty ((extendScalars (SplittingField τ) τ.endFieldRep).Equiv (wordRep ι w)) := by
  let : Algebra (ZMod 2) (SplittingField τ) := ZMod.algebra _ 2
  let : IsAbsolutelyIrreducible τ.endFieldRep := endFieldRep_isAbsolutelyIrreducible τ
  let : IsIrreducible (extendScalars (SplittingField τ) τ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension τ.endFieldRep (SplittingField τ)
  let ι : Matrix.PSL3Four.F →+* SplittingField τ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := Matrix.PSL3Four.F)
      (M := SplittingField τ)).toRingHom
  have hcard : Nat.card Matrix.PSL3Four.F = 2 ^ 2 := by
    simpa using Matrix.PSL3Four.card_F
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_word_equiv ι 2 hcard
    (extendScalars (SplittingField τ) τ.endFieldRep)
  have hp := word_rotate_iff_schurDegree_dvd τ ι w (hw ▸ hcard)
    (fun v hv => wordRep_isIrreducible ι 2 hcard v (hv.trans hw))
    (fun u v hu hv h =>
      (wordRep_equiv_iff ι 2 hcard u v (hu.trans hw) (hv.trans hw)).mp h) ⟨e⟩
  have hdim : 16 = Representation.schurDegree 2 τ * wordDegree w := by
    rw [← hd, Representation.finrank_eq_schurDegree_mul 2 τ (SplittingField τ),
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  obtain ⟨hs, hw⟩ := sixteen_word w hw _ hdim hp
  exact ⟨hs, ι, w, hw, ⟨e⟩⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The actual point-submodule inflation has quadratic Schur field and an
adjoint tensor-word identification. This is the consumer of the local catalogue. -/
theorem point_submodule_adjoint_orbit (σ : Representation (ZMod 2) M22 V)
    (S : Subrepresentation (pointRestriction σ)) [S.toRepresentation.IsIrreducible]
    (hd : Module.finrank (ZMod 2) S.toSubmodule = 16) :
    let τ : Representation (ZMod 2) Matrix.PSL3Four.SL S.toSubmodule :=
      S.toRepresentation.comp pointSL
    letI : τ.IsIrreducible :=
      (irreducible_comp_surjective_iff pointSL pointSL_surjective S.toRepresentation).mpr
        inferInstance
    Representation.schurDegree 2 τ = 2 ∧
      ∃ (ι : Matrix.PSL3Four.F →+* SplittingField τ) (w : List Factor),
        (w = [.adjoint, .trivial] ∨ w = [.trivial, .adjoint]) ∧
        Nonempty ((extendScalars (SplittingField τ) τ.endFieldRep).Equiv (wordRep ι w)) := by
  dsimp only
  let : IsIrreducible (S.toRepresentation.comp pointSL) :=
    (irreducible_comp_surjective_iff pointSL pointSL_surjective S.toRepresentation).mpr
      inferInstance
  exact absolute_adjoint_orbit _ hd

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
