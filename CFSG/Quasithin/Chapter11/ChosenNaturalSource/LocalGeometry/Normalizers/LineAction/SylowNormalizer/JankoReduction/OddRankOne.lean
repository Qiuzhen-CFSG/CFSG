module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.SylowModels
public import Theory.SpecificGroups.PSL2.FourNormalizer
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.GroupTheory.SpecificGroups.DihedralAut

/-!
# Odd square-field exclusions for the actual moved component

A Sylow two-subgroup of odd PSL₂ contains a self-centralizing four-group.
When its order is at least eight it is dihedral with a two-group of
automorphisms, so its normalizer is itself. The outer group over a field
of prime-square order is also a two-group. Consequently the automorphism
stabilizer of the literal Sylow is a two-group, contradicting the nontrivial
odd complement action in the moved-component quotient.

The final application starts with the original Sylow-normalizer escape.
J₁ recognition and terminal geometry remain with qt-d-1222-natural-line-action.
Source: Aschbacher--Smith 3.3.12, printed pp.589--590, case (8) of A.3.12.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem odd_psl2_sylow_centralizer_le
    {F : Type*} [Field F] [Finite F]
    (ho : GorensteinWalter.IsOddPrimePower (Nat.card F)) (P : Sylow 2 PSL(2,F)) :
    centralizer (P : Set PSL(2,F)) ≤ (P : Subgroup PSL(2,F)) := by
  obtain ⟨m,hm,⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
  obtain ⟨B,hBP,hB⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup PSL(2,F)) hm e
  let := hB
  exact (centralizer_le hBP).trans ((Theory.PSL2.FourNormalizer.four_centralizer ho B).le.trans hBP)

private theorem odd_psl2_large_sylow_self_normalizing
    {F : Type*} [Field F] [Finite F]
    (ho : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : 8 ∣ Nat.card PSL(2,F)) (P : Sylow 2 PSL(2,F)) :
    normalizer (P : Set PSL(2,F)) = (P : Subgroup PSL(2,F)) := by
  obtain ⟨m,hm,⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
  have hm2 : 2 ≤ m := by
    have hd := P.pow_dvd_card_of_pow_dvd_card (n := 3) h8
    by_contra hh
    have he : m = 1 := by omega
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card,he] at hd
    norm_num at hd
  have hauto : IsPGroup 2 (MulAut P) :=
    (DihedralGroup.isPGroup_mulAut_of_two_lt
      (show 2 < 2^m by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < m by omega))
      (P.isPGroup'.of_equiv e)).of_equiv (MulAut.congr e).symm
  have hnorm : IsPGroup 2 (normalizer (P : Set PSL(2,F))) := by
    intro g
    obtain ⟨n,hn⟩ := hauto ((P : Subgroup PSL(2,F)).normalizerMonoidHom g)
    have hc : (g : PSL(2,F)) ^ (2^n) ∈ centralizer (P : Set PSL(2,F)) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have hh := congrArg (fun a : MulAut P => ((a ⟨x,hx⟩ : P) : PSL(2,F))) hn
      rw [← map_pow] at hh
      change (g : PSL(2,F)) ^ (2^n) * x * ((g : PSL(2,F)) ^ (2^n))⁻¹ = x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    obtain ⟨k,hk⟩ := P.isPGroup' ⟨_,odd_psl2_sylow_centralizer_le ho P hc⟩
    refine ⟨n+k,Subtype.ext ?_⟩
    change (g : PSL(2,F)) ^ (2^(n+k)) = 1
    rw [Nat.pow_add,pow_mul]
    exact congrArg Subtype.val hk
  exact P.is_maximal' hnorm (P : Subgroup PSL(2,F)).le_normalizer

private theorem odd_square_eight_dvd {p : ℕ} (hp : p.Prime) (ho : Odd p)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = p^2) :
    8 ∣ Nat.card PSL(2,F) := by
  have hmod : p^2 % 8 = 1 := by
    have hodd := Nat.odd_iff.mp ho
    have hm := Nat.mod_lt p (by decide : 0 < 8)
    have he : p % 8 % 2 = 1 := by omega
    rw [Nat.pow_mod]
    interval_cases h : p % 8 <;> norm_num at *
  have hsub : 8 ∣ p^2-1 := by omega
  have hplus : 2 ∣ p^2+1 := by
    have he := Nat.odd_iff.mp (ho.pow (n := 2))
    omega
  have hs : (p^2)^2 - 1 = (p^2-1)*(p^2+1) := by
    nlinarith [hp.two_le,Nat.sub_add_cancel (show 1 ≤ p^2 by nlinarith [hp.two_le]),
      Nat.sub_add_cancel (show 1 ≤ (p^2)^2 from Nat.one_le_pow _ _ (pow_pos hp.pos _))]
  rw [GorensteinWalter.psl2_card_formula F ⟨p,2,hp,ho,by decide,hF⟩,hF,hs]
  exact Nat.dvd_div_of_mul_dvd (dvd_mul_of_dvd_right (Nat.mul_dvd_mul hsub hplus) _)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The full square-field PSL₂ row is excluded in the literal K/O₂(K). -/
theorem quotient_not_odd_square_psl2 {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) 2 (p^2) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  exact E.quotient_not_equiv_self_normalizing_outer_two
    (odd_psl2_large_sylow_self_normalizing ⟨p,2,hp,ho,by decide,hF⟩
      (odd_square_eight_dvd hp ho hF))
    (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho (by decide) hF)
    ⟨e⟩

end MovedComponent

/-- The original escape supplies the exclusion without a changed quotient or Sylow. -/
theorem exists_moved_component_not_odd_square_psl2 (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A, ∀ p : ℕ, p.Prime → Odd p →
      ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) 2 (p^2) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,fun _ hp ho => E.quotient_not_odd_square_psl2 hp ho⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
