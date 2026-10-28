module
public import Theory.GroupTheory.SemidihedralWreathedTwoFiveCenter
public import ABG.ChapterII.Section2.FullSylowShapes
public import Theory.SpecificGroups.PSL3.OddSylowCenter

/-!
# Actual odd PSL₃ two-five overgroups lie in an involution centralizer

The odd-index GL₂ involution centralizer and the actual central projective
projection give every supplied PSL₃ Sylow its semidihedral or wreathed
presentation. The two-five fusion theorem therefore places the full
normalizer of the original overgroup in the centralizer of its supplied
central Sylow involution. No field congruence or Sylow-shape premise remains.

Source: ABG II.1 Propositions 1–2 and II.2 Lemma 1; Aschbacher–Smith
A.3.21(a) and the odd ternary row in 6.1.4.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.TwoFiveSylow
variable (F : Type*) [Field F] [Finite F]

private theorem sylow_shape (ho : Odd (Nat.card F)) (T : Sylow 2 PSL(3,F)) :
    Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
  have h2 := Field.two_ne_zero_of_odd_card F ho
  let P : Sylow 2 (GL (Fin 2) F) := Classical.choice inferInstance
  let S : Sylow 2 SL(3,F) := Classical.choice inferInstance
  have hi := odd_index_centralizer_of_one_involution_class
    (SL3.standardInvolution F) (SL3.standardInvolution_orderOf F h2)
    (fun z hz => SL3.involution_isConj_standard F z hz h2)
  obtain ⟨e⟩ := sylow_equiv_of_odd_index _ hi
    (SL3.standardInvolutionCentralizerEquiv F h2).symm S P
  have hk : Nat.Coprime 2 (Nat.card (projection F).ker) := by
    rw [projection_ker]
    exact Nat.coprime_two_left.mpr (SL3.odd_card_center F)
  let eT := Sylow.equivOfSurjectiveCoprime (projection F) (projection_surjective F) hk S T
  let ePT : P ≃* T := e.symm.trans eT
  rcases ABG.full_GL2_sylow_shape F ho P with h | ⟨n,h⟩
  · exact .inl (ABG.semidihedral_equiv ePT h)
  · exact .inr ⟨n,ABG.wreathed_equiv ePT h⟩

/-- The full normalizer of the actual two-five overgroup fixes the supplied
central involution of the original full Sylow in odd PSL₃. -/
theorem normalizer_le_centralizer (ho : Odd (Nat.card F))
    (T : Sylow 2 PSL(3,F)) (H : Subgroup PSL(3,F))
    (hTH : (T : Subgroup PSL(3,F)) ≤ H) {k : ℕ}
    (hd : Nat.card H ∣ 2^k*5) (z : T)
    (hz : orderOf z = 2) (hc : z ∈ center T) :
    normalizer (H : Set PSL(3,F)) ≤ centralizer ({(z : PSL(3,F))} : Set PSL(3,F)) :=
  Theory.GroupTheory.TwoFiveSylow.normalizer_le_involution_centralizer
    T (sylow_shape F ho T) H hTH hd z hz hc

/-- Every automorphism of the actual PSL₃ carrier preserving the overgroup
fixes the same central Sylow involution, including outer automorphisms. -/
theorem automorphism_fixes_involution (ho : Odd (Nat.card F))
    (T : Sylow 2 PSL(3,F)) (H : Subgroup PSL(3,F))
    (hTH : (T : Subgroup PSL(3,F)) ≤ H) {k : ℕ}
    (hd : Nat.card H ∣ 2^k*5) (z : T)
    (hz : orderOf z = 2) (hc : z ∈ center T)
    (φ : MulAut PSL(3,F)) (hφ : H.map φ.toMonoidHom = H) :
    φ (z : PSL(3,F)) = z :=
  Theory.GroupTheory.TwoFiveSylow.automorphism_fixes_involution
    T (sylow_shape F ho T) H hTH hd z hz hc φ hφ

end Matrix.PSL3.TwoFiveSylow
