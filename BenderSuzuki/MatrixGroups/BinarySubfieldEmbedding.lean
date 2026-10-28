module

public import BenderSuzuki.Converse.PSL2
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Binary PSL2 subfield embeddings

For nonzero degrees d dividing n, Mathlib constructs an algebra embedding
GF(2^d) into GF(2^n) from the finite-field finranks. Applying it entrywise gives
an injection of special linear groups. In characteristic two the scalar
center of SL2 is trivial, so the canonical quotient maps identify SL2 with
PSL2. Transporting the entrywise map through these exact quotient
equivalences gives the group embedding.

This is the concrete subfield obstruction used to force prime exponents in
Thompson's binary minimal-simple family. Properness is intentionally left to
the order comparison in the consumer.

Source: the standard finite-field subfield theorem and the characteristic-two
SL2 center calculation in BenderSuzuki.Converse.PSL2.
-/

namespace BenderSuzuki.MatrixGroups

/-- A dividing binary field degree induces an injective PSL2 homomorphism. -/
public theorem exists_binary_psl2_embedding
    {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) (hdiv : d ∣ n) :
    ∃ f : PSL2MatrixGroup (GaloisField 2 d) →* PSL2MatrixGroup (GaloisField 2 n),
      Function.Injective f := by
  have hdegree : Module.finrank (ZMod 2) (GaloisField 2 d) ∣
      Module.finrank (ZMod 2) (GaloisField 2 n) := by
    rw [GaloisField.finrank 2 hd, GaloisField.finrank 2 hn]
    exact hdiv
  obtain ⟨i⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdegree
  let eD : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 d) ≃*
      PSL2MatrixGroup (GaloisField 2 d) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi _)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let eN : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) ≃*
      PSL2MatrixGroup (GaloisField 2 n) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi _)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let slMap : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 d) →*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    Matrix.SpecialLinearGroup.map i.toRingHom
  have hslMap : Function.Injective slMap := by
    intro a b hab
    ext r c
    apply i.injective
    exact congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) =>
      x r c) hab
  refine ⟨(eN.toMonoidHom.comp slMap).comp eD.symm.toMonoidHom, ?_⟩
  exact eN.injective.comp (hslMap.comp eD.symm.injective)

end BenderSuzuki.MatrixGroups
