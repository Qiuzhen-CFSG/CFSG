module

public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Arithmetic
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.SmallBranch
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.ExceptionalIsomorphisms
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Eight
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.FieldRestriction

/-!
# Recognition from dihedral involution centralizers

Preparatory results for Aschbacher–Smith, *The Classification of Quasithin
Groups*, I.4.1, printed pp. 415–416: the exact hypotheses, the Sylow
reduction, the Fermat/Mersenne arithmetic, and the order-two
Brauer–Suzuki–Wall branch with both alternating-group alternatives.

The local Brauer–Suzuki–Wall data, the PSL₂ recognition, and the exceptional
model identifications are supplied by the descendant modules imported here.
-/

namespace CFSG.Quasithin

open GorensteinWalter

namespace DihedralInvolutionCentralizerHypotheses

variable {G : Type*} [Group G] [Finite G] {n : ℕ}

/-- The `n = 2` branch of Aschbacher–Smith I.4.1. -/
public theorem recognition_of_two
    (h : DihedralInvolutionCentralizerHypotheses G 2) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨b, _hbt, _hbH, hbK⟩ := h.exists_brauerSuzukiWallHypotheses
  exact alternating_four_or_five_of_bsw_card_two b (by simpa using hbK)

/-- The `n = 3` branch of Aschbacher–Smith I.4.1. -/
public theorem recognition_of_three
    (h : DihedralInvolutionCentralizerHypotheses G 3) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) :=
  h.recognize_eight

/-- The prime-field branch of Aschbacher–Smith I.4.1. -/
public theorem recognition_of_three_lt
    (h : DihedralInvolutionCentralizerHypotheses G n) (hn : 3 < n) :
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧
      Nonempty (G ≃* PSL2 (ZMod p)) := by
  obtain ⟨b, _hbt, _hbH, hbK⟩ := h.exists_brauerSuzukiWallHypotheses
  have hbFour : 4 ≤ Nat.card b.K := by
    rw [hbK]
    have hn2 : 2 ≤ n := h.two_le
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨F, hF, hFin, hOdd, ⟨e⟩⟩ :=
    exists_field_mulEquiv_psl2_of_bsw_four_le_card_K b hbFour
  let _ := hF
  let _ := hFin
  obtain ⟨p, _hcard, hp, he⟩ := h.prime_field_equiv_of_three_lt hOdd e hn
  exact ⟨p, hp, he⟩

/-- The complete recognition theorem of Aschbacher–Smith I.4.1.

The first two disjuncts retain the actual small exceptional groups, including
the nonsimple `A₄` alternative. The last disjunct records the actual prime
field model and the Fermat/Mersenne restriction. -/
public theorem recognition
    (h : DihedralInvolutionCentralizerHypotheses G n) :
    (n = 2 ∧
        (Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
          Nonempty (G ≃* alternatingGroup (Fin 5)))) ∨
      (n = 3 ∧
        (Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          Nonempty (G ≃* alternatingGroup (Fin 6)))) ∨
      (3 < n ∧ ∃ p : ℕ, IsFermatOrMersennePrime p ∧
        Nonempty (G ≃* PSL2 (ZMod p))) := by
  by_cases hn2 : n = 2
  · exact Or.inl ⟨hn2, recognition_of_two (hn2 ▸ h)⟩
  by_cases hn3 : n = 3
  · exact Or.inr (Or.inl ⟨hn3, recognition_of_three (hn3 ▸ h)⟩)
  have hnle : 2 ≤ n := h.two_le
  have hn : 3 < n := by omega
  exact Or.inr (Or.inr ⟨hn, recognition_of_three_lt h hn⟩)

end DihedralInvolutionCentralizerHypotheses

namespace ChapterI

/-- The unbundled source-style statement of Aschbacher–Smith I.4.1. -/
public theorem lemma_I_4_1
    {G : Type*} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (z : G) (hz : IsInvolution z)
    (hclass : ∀ u : G, IsInvolution u → ∃ g : G, g * u * g⁻¹ = z)
    (hC : Nonempty
      (Subgroup.centralizer ({z} : Set G) ≃* DihedralGroup (2 ^ (n - 1)))) :
    (n = 2 ∧
        (Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
          Nonempty (G ≃* alternatingGroup (Fin 5)))) ∨
      (n = 3 ∧
        (Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          Nonempty (G ≃* alternatingGroup (Fin 6)))) ∨
      (3 < n ∧ ∃ p : ℕ, IsFermatOrMersennePrime p ∧
        Nonempty (G ≃* GorensteinWalter.PSL2 (ZMod p))) := by
  exact DihedralInvolutionCentralizerHypotheses.recognition {
    two_le := hn
    z := z
    involution := hz
    involutions_conjugate := hclass
    centralizer_equiv := hC
  }

end ChapterI
end CFSG.Quasithin
