module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.OuterRank
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL3.OuterSolvable.CyclicDiagonal
public import Theory.SpecificGroups.PSL3.OuterSolvable.CyclicNormal
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.GroupTheory.CyclicNormalOddQuotient.CyclicByTwo
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The outer three-rank of an even linear three-dimensional model

For a binary field of odd degree, the projective three-rank-one hypothesis
forces the field order to be `2 mod 3`: even degree would contain the explicit
projective elementary subgroup of order nine.  In the surviving case the
linear diagonal image in the actual outer quotient is trivial, since cubing
is bijective on the field units.  Standard automorphism coverage then leaves
only the cyclic field automorphisms and the commuting graph involution, so
all Sylow three-subgroups of the actual outer quotient are cyclic.

This is the conditional intrinsic contract used by the Chapter 15 source
assembly.  The coverage premise is retained explicitly; the theorem does not
assert arbitrary-automorphism coverage on its own.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, printed
pp.33 and 1137 (PDF pp.44 and 1154); GLS3, Theorem 2.5.12 and Section 2.7.
-/

public section

open Matrix Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Matrix.PSL3.OuterSolvable

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne

private theorem fieldSL_toGL {F : Type*} [Field F] (τ : F ≃+* F) (x : SL(3,F)) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map τ.toRingHom x) =
      GeneralLinearGroup.map τ.toRingHom (SpecialLinearGroup.toGL x) := Units.ext rfl

private theorem field_linearConj {F : Type*} [Field F] (τ : F ≃+* F) (A : GL (Fin 3) F) :
    fieldAction F τ * linearConj F A =
      linearConj F (GeneralLinearGroup.map τ.toRingHom A) * fieldAction F τ := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, linearConj_mk]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [fieldSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
      linearConjSL_toGL, fieldSL_toGL]

private theorem field_commute_graph {F : Type*} [Field F] (τ : F ≃+* F) :
    Commute (fieldAction F τ) (graph F) := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, graph_mk]
    rw [map_inv]
    congr 2

private theorem diagonal_outer_eq_bot {F : Type*} [Field F] [Finite F] {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) (hfodd : Odd f) :
    innerDiagonalOuter F = ⊥ := by
  have hcop : (Nat.card Fˣ).Coprime 3 := by
    rw [Nat.card_units, hcard]
    apply Nat.Coprime.symm
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hm := Nat.BinaryTorusParity.two_pow_mod_three f
    have ho := Nat.odd_iff.mp hfodd
    have hp : 0 < (2 : ℕ) ^ f := pow_pos (by decide) _
    simp only [ho, show ¬ (1 : ℕ) = 0 by decide, if_false] at hm
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  apply bot_unique
  rintro x ⟨g, rfl⟩
  obtain ⟨u, hu⟩ := hcop.pow_left_bijective.surjective (GeneralLinearGroup.det g)
  change u ^ 3 = GeneralLinearGroup.det g at hu
  let s : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) u⁻¹
  let h : GL (Fin 3) F := s * g
  have hsdet : GeneralLinearGroup.det s = (u⁻¹) ^ 3 := by
    simp [s]
  have hdet : GeneralLinearGroup.det h = 1 := by
    rw [map_mul, hsdet, ← hu]
    simp
  have hdet' : h.val.det = 1 := congrArg Units.val hdet
  let z : SL(3,F) := ⟨h.val, hdet'⟩
  have hz : SpecialLinearGroup.toGL z = h := Units.ext rfl
  have hinner : QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
      (linearConj F h) = 1 := by
    rw [← hz, linearConj_toGL]
    exact (QuotientGroup.eq_one_iff _).mpr
      ⟨QuotientGroup.mk' (Subgroup.center SL(3,F)) z, rfl⟩
  have hs : linearConj F s = 1 := by
    exact Matrix.PSL3.OddInvolutionFixed.linearConj_scalar (u⁻¹)
  change QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F g) = 1
  calc
    QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F g) =
        QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
          (linearConj F s * linearConj F g) := by rw [hs, one_mul]
    _ = QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F h) := by
      rw [← map_mul]
    _ = 1 := hinner

/-- A binary `PSL₃` model with intrinsic three-rank one has outer three-rank
at most one, assuming the explicit standard-automorphism coverage premise. -/
theorem outer_three_rank_le_one_of_psl3_even
    {F : Type*} [Field F] [Finite F] {f : ℕ} (_hf : 1 ≤ f)
    (hcard : Nat.card F = 2 ^ f) [IsSimpleGroup PSL(3,F)]
    (_hna : ¬ IsMulCommutative PSL(3,F))
    (hr : primeRank 3 PSL(3,F) = 1)
    (hcover : standard F = ⊤) :
    primeRank 3 (MulAut.Outer PSL(3,F)) ≤ 1 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfodd : Odd f := by
    rcases Nat.even_or_odd f with he | ho
    · have htwo := Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hcard he
      omega
    · exact ho
  have hC := diagonal_outer_eq_bot hcard hfodd
  let I := MulAut.innerSubgroup PSL(3,F)
  let q : MulAut PSL(3,F) →* MulAut.Outer PSL(3,F) := QuotientGroup.mk' I
  let D : Subgroup (MulAut.Outer PSL(3,F)) := (q.comp (fieldAction F)).range
  let t : MulAut.Outer PSL(3,F) := q (graph F)
  let Z : Subgroup (MulAut.Outer PSL(3,F)) := Subgroup.zpowers t
  let : IsCyclic (F ≃+* F) :=
    BenderSuzuki.MatrixGroups.HermitianForm.finiteFieldAut_isCyclic
  have hD : IsCyclic D := by
    exact isCyclic_of_surjective (q.comp (fieldAction F)).rangeRestrict
      (q.comp (fieldAction F)).rangeRestrict_surjective
  let : IsCyclic D := hD
  have hlin (m : GL (Fin 3) F) : q (linearConj F m) = 1 := by
    have hx : q (linearConj F m) ∈ innerDiagonalOuter F := ⟨m, rfl⟩
    rw [hC, mem_bot] at hx
    exact hx
  have hfield (τ : F ≃+* F) (A : GL (Fin 3) F) :
      fieldAction F τ * linearConj F A =
        linearConj F (GeneralLinearGroup.map τ.toRingHom A) * fieldAction F τ :=
    field_linearConj τ A
  have hgraph (A : GL (Fin 3) F) :
      graph F * linearConj F A =
        linearConj F (Matrix.PSL3.OddInvolutionFixed.inverseTransposeGL A) * graph F :=
    Matrix.PSL3.OddInvolutionFixed.graph_linearConj A
  have hcomm (τ : F ≃+* F) : Commute (fieldAction F τ) (graph F) :=
    field_commute_graph τ
  have hgen : D ⊔ Z = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I x
    obtain ⟨m, τ, ha | ha⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization
      F hfield (fun A => ⟨_, hgraph A⟩) hcomm a (hcover ▸ mem_top a)
    · rw [ha, map_mul, hlin, one_mul]
      have hd : q (fieldAction F τ) ∈ D := ⟨τ, rfl⟩
      exact Subgroup.mul_mem_sup hd (Subgroup.one_mem _)
    · rw [ha, map_mul, map_mul, hlin, one_mul]
      have hd : q (fieldAction F τ) ∈ D := ⟨τ, rfl⟩
      exact Subgroup.mul_mem_sup hd (Subgroup.mem_zpowers _)
  have ht : t ^ 2 = 1 := by
    dsimp [t]
    rw [← map_pow, Matrix.PSL3.OuterSolvable.graph_sq, map_one]
  have hDt : D ≤ Subgroup.centralizer ({t} : Set (MulAut.Outer PSL(3,F))) := by
    rintro d ⟨τ, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg q (hcomm τ)
  have hDz : D ≤ Subgroup.centralizer (Z : Set (MulAut.Outer PSL(3,F))) := by
    intro d hd z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hdt : Commute d t := Subgroup.mem_centralizer_singleton_iff.mp (hDt hd)
    exact (hdt.zpow_right k).symm
  have hjoincomm : IsMulCommutative (D ⊔ Z : Subgroup (MulAut.Outer PSL(3,F))) := by
    apply Subgroup.le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact Subgroup.le_centralizer_iff.mpr
        (sup_le (show D ≤ Subgroup.centralizer (D : Set (MulAut.Outer PSL(3,F))) from
          Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
          (Subgroup.le_centralizer_iff.mp hDz))
    · exact Subgroup.le_centralizer_iff.mpr
        (sup_le hDz (show Z ≤
          Subgroup.centralizer (Z : Set (MulAut.Outer PSL(3,F))) from
          Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance))
  have htopcomm : IsMulCommutative (⊤ : Subgroup (MulAut.Outer PSL(3,F))) := hgen ▸ hjoincomm
  let : IsMulCommutative (MulAut.Outer PSL(3,F)) := ⟨⟨by
    intro x y
    exact congrArg Subtype.val (htopcomm.is_comm.comm
      (⟨x, mem_top _⟩ : (⊤ : Subgroup (MulAut.Outer PSL(3,F))))
      (⟨y, mem_top _⟩ : (⊤ : Subgroup (MulAut.Outer PSL(3,F)))))⟩⟩
  let P : Sylow 3 (MulAut.Outer PSL(3,F)) := Classical.choice inferInstance
  have hP : IsCyclic P := by
    apply Theory.GroupTheory.isCyclic_pSubgroup_of_cyclic_sup_involution D t ht hgen 3
      (by decide) (P : Subgroup (MulAut.Outer PSL(3,F))) P.isPGroup'
  exact P.primeRank_le_one_of_isCyclic hP

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
