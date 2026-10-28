module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SmallComponents
/-!
# The smaller source model inside M₁₁

The original surviving source list contains only A₆, PSL₃(2), PSL₃(3),
M₁₁ and the Fermat/Mersenne prime-linear family. Lagrange excludes the
linear rows inside M₁₁: the only possible large prime is 11, which is
neither Fermat nor Mersenne. Thus a proper inclusion forces A₆.
Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
private theorem eleven_not_fermat_mersenne : ¬IsFermatOrMersennePrime 11 := by
  intro h
  have hp (k:ℕ) : 2^k≠10 ∧ 2^k≠12 := by
    have hcases : k<4 ∨ 4≤k := lt_or_ge k 4
    rcases hcases with hk | hk
    · interval_cases k <;> norm_num
    · have hh := Nat.pow_le_pow_right (by decide : 0<2) hk
      norm_num at hh
      omega
  rcases h.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · exact (hp (2^k)).1 (by omega)
  · exact (hp k).2 hk.symm

theorem small_model_in_mathieu {G : Type*} [Group G] [Finite G]
    {K C : Subgroup G} (hKC : K≤C) (hK : IsSmallRemainingComponent K)
    (hC : Nonempty (C≃*Sporadic.Mathieu.M11)) :
    K=C ∨ Nonempty (K≃*alternatingGroup (Fin 6)) := by
  obtain ⟨eC⟩ := hC
  have hc : Nat.card C=7920 := (Nat.card_congr eC.toEquiv).trans Sporadic.Mathieu.m11_order
  have hd := card_dvd_of_le hKC
  rw [hc] at hd
  rcases hK with h | h | h | h | h
  · exact .inr h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_PSL] at hd
    norm_num at hd
  · obtain ⟨e⟩ := h
    have hh := ChapterA.Section03.OddPrime.SourceModels.SmallComponents.small_card
      (Or.inl ⟨e⟩)
    rcases hh with hh | hh
    · rw [hh] at hd; norm_num at hd
    · exact .inl (eq_of_le_of_card_ge hKC (by omega))
  · obtain ⟨e⟩ := h
    exact .inl (eq_of_le_of_card_ge hKC (by
      rw [hc,Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order]))
  · obtain ⟨p,hp,hlarge,⟨e⟩⟩ := h
    let : Fact p.Prime := ⟨hp.1⟩
    have ho : Odd p := hp.1.odd_of_ne_two (by omega)
    have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F:=ZMod p) (by simpa using ho)
    rw [Nat.card_zmod] at hcard
    have hpc : p ∣ Nat.card PSL(2,ZMod p) := by
      have hmul : p∣2*Nat.card PSL(2,ZMod p) := by rw [mul_comm 2,hcard]; exact dvd_mul_right _ _
      rcases hp.1.dvd_mul.mp hmul with htwo | hh
      · have hh := Nat.le_of_dvd (by decide : 0<2) htwo
        omega
      · exact hh
    have hpd : p∣7920 := hpc.trans (by simpa only [Nat.card_congr e.toEquiv] using hd)
    have hfac : p∈Nat.primeFactors 7920 := Nat.mem_primeFactors.mpr ⟨hp.1,hpd,by decide⟩
    have hf : Nat.primeFactors 7920={2,3,5,11} := by decide +kernel
    rw [hf] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    have he : p=11 := by omega
    exact (eleven_not_fermat_mersenne (he ▸ hp)).elim
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
