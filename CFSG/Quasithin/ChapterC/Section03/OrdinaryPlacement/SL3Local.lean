module

public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.GroupTheory.PrimeRankZero

/-!
# The degree-three linear local obstruction in C.3.5

The full normalizer of the actual nonidentity two-subgroup is conjugate
into a point or line parabolic of PSL₃ over a finite binary field. Every
perfect subgroup of either parabolic has odd-prime rank at most one.
Consequently a faithful perfect group of five-rank at least two cannot
normalize that two-subgroup. The field of order two is handled by its
ambient projective group order, 168.

The last form retains a homomorphism with a two-group kernel, as supplied
by the original span inside an ordinary component and its central quotient.
Only this two-kernel is removed; no assertion about discarding the scalar
three-kernel of the special-linear projection is used.

Source: Aschbacher–Smith C.3.5, printed p.150, using the literal parabolic
geometry of the degree-three linear family.
-/

public section
open Subgroup Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.SL3Local
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A perfect group of five-rank two cannot normalize any nontrivial
two-subgroup in the actual binary degree-three projective model. -/
theorem no_perfect_five_rank_two_in_two_normalizer
    (P : Subgroup PSL(3,F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (hr : 2 ≤ primeRank 5 A) (f : A →* PSL(3,F)) (hf : Function.Injective f)
    (hn : f.range ≤ normalizer (P : Set PSL(3,F))) : False := by
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨n,_,hcard⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  by_cases hn1 : (n : ℕ) = 1
  · have hcardF : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    have hz : primeRank 5 PSL(3,F) = 0 :=
      PrimeRank.eq_zero_iff_not_dvd_card.mpr (by
        rw [card_projective F,hcardF]
        norm_num)
    have hb := primeRank_le_of_injective 5 f hf
    omega
  · obtain ⟨g,point,hg⟩ :=
      MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F n.pos hF
        (normalizer (P : Set PSL(3,F))) ⟨P,hne,hp,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp f
    have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
      refine le_trans ?_ hg
      rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem _ (hn ⟨a,rfl⟩)
    have hfour : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (show 2 ≤ (n : ℕ) by have := n.pos; omega)
    apply PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic F
      (p := 5) (by decide) hr hfour j ((MulAut.conj g).injective.comp hf)
    cases point
    · exact Or.inr hj
    · exact Or.inl hj

/-- The normalizer bound with a literal two-kernel homomorphism. This
matches the source span map through the ordinary component central quotient. -/
theorem no_perfect_five_rank_two_with_two_kernel
    (P : Subgroup PSL(3,F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (hr : 2 ≤ primeRank 5 A) (f : A →* PSL(3,F)) (hk : IsPGroup 2 f.ker)
    (hn : f.range ≤ normalizer (P : Set PSL(3,F))) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hc : Nat.Coprime 5 (Nat.card f.rangeRestrict.ker) := by
    have he : f.rangeRestrict.ker = f.ker := by
      ext a
      exact Subtype.ext_iff
    rw [he]
    obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp hk
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hb := primeRank_le_of_coprime_ker 5 f.rangeRestrict hc
  apply no_perfect_five_rank_two_in_two_normalizer P hp hne (hr.trans hb)
    f.range.subtype f.range.subtype_injective
  simpa only [range_subtype] using hn

end CFSG.Quasithin.ChapterC.OrdinaryPlacement.SL3Local
