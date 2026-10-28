module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.NumberTheory.BinaryTorusParity

/-!
# A shared prime obstruction for proper local components in binary PSL₃

The full-Sylow parabolic placement identifies the smaller component's actual
two-core quotient with SL₂ over the containing field. Low cubic rank forces
odd field degree. Any prime in its split torus is then different from three
and has rank at least two in the containing PSL₃, while still dividing the
smaller quotient. No field-degree equality between arbitrary sections is used.

The half-Sylow enlargement consumer applies this to the literal image of the
original conjugate component modulo the containing two-core.
Source: Aschbacher--Smith A.3.12 and 10.2.6, printed pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The intrinsic quotient of a proper local component uses the containing field. -/
theorem linear_three_local_core_quotient {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hne : B ≠ ⊤) :
    Nonempty ((B ⧸ pCore 2 B) ≃* SL(2,F)) := by
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hn S B hB hne
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr (pCore 2 B) _ a (pCore_map_iso 2 a)
  suffices h : Nonempty (((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) by
    exact ⟨aq.trans h.some⟩
  rcases hg with hg | hg
  · rw [hg]
    exact ⟨pointLocalCoreQuotientEquiv F⟩
  · rw [hg]
    exact ⟨lineLocalCoreQuotientEquiv F⟩

/-- A proper local component in binary PSL₃ shares a prime of rank at least two
with its containing group, including every odd field degree. -/
theorem linear_three_local_shared_prime_rank {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hne : B ≠ ⊤)
    (h3 : primeRank 3 PSL(3,F) ≤ 1) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (B ⧸ pCore 2 B) ∧
      2 ≤ primeRank p PSL(3,F) := by
  have ho : Odd n := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hF he
    omega
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.card F - 1 ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with he | he
    · subst p
      have h2 : 2 ∣ Nat.card F := by
        rw [hF]
        exact dvd_pow_self 2 (by omega : n ≠ 0)
      have hzero := Nat.mod_eq_zero_of_dvd h2
      have hone := Nat.mod_eq_zero_of_dvd hd
      omega
    · exact Nat.odd_iff.mpr he
  have hp3 : p ≠ 3 := by
    intro he
    subst p
    have hcop := Nat.BinaryTorusParity.coprime_three_sub_one ho
    rw [←hF] at hcop
    exact Nat.prime_three.coprime_iff_not_dvd.mp hcop hd
  obtain ⟨e⟩ := linear_three_local_core_quotient hF hn S B hB hne
  refine ⟨p,hp,hpodd,?_,Matrix.PSL3.SplitPrimeRank.projective_rank F hp3 hd⟩
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula]
  have hfac : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ Nat.card F)
    have hsq := Nat.sub_add_cancel (by nlinarith : 1 ≤ Nat.card F ^ 2)
    nlinarith
  rw [hfac]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
