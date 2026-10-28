module

public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import GorensteinWalter.PGL2LowReflectedToriCard
public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Cubic fixers at the remaining odd-prime parameters

At p congruent to 11 or 13 modulo 24, the low-two-part torus in PGL₂(p)
has order prime to three. Its reflected normalizer is the centralizer of
the marked outer involution. Outer-involution fusion transports this
calculation to every outer involution. Consequently an involutory
automorphism of PSL₂(p) fixing an element of order three must be inner.

The cubic and automorphism are supplied elements with their original
markings. This calculation is used in the collapsed normalizer case of
Aschbacher--Smith 10.2.5, printed p.748; it asserts no nontriviality or
placement of the original full module in the containing component.
-/

public noncomputable section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.CubicFixer

/-- Outer involution centralizers have order prime to three at the two
remaining prime congruences, with the canonical PSL₂ inclusion retained. -/
theorem outer_centralizer_not_three_dvd {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hF : Nat.card F = p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (a : PGL2 F) (ha : IsInvolution a)
    (hout : a ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    ¬ 3 ∣ Nat.card (centralizer ({a} : Set (PGL2 F))) := by
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  have hlarge : 3 < Nat.card F := by have := Nat.mod_le p 24; omega
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p,1,Fact.out,hp,by decide,by simpa using hF⟩
  let P : Sylow 2 (PGL2 F) := Classical.choice inferInstance
  obtain ⟨m,_,⟨d⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd P
  obtain ⟨D⟩ := pgl2_low_reflected_tori_card_four F hodd hlarge P d
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd hlarge
  obtain ⟨g,hg⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate_of_odd_prime_power
    F hodd D.s_involution ha (hJ ▸ D.s_not_mem_commutator) hout)
  have he : (centralizer ({D.s} : Set (PGL2 F))).map (MulAut.conj g).toMonoidHom =
      centralizer ({a} : Set (PGL2 F)) := by
    rw [map_centralizer_equiv,Set.image_singleton]
    change centralizer ({g * D.s * g⁻¹} : Set (PGL2 F)) = _
    rw [hg]
  rw [←he,card_map_of_injective (MulAut.conj g).injective,D.centralizer_eq]
  obtain ⟨eD⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted D.U D.w D.U_cyclic
    (by simpa only [pow_two] using D.w_involution) D.w_not_mem_U D.w_inverts_U
  rw [Nat.card_congr eD.toEquiv,DihedralGroup.nat_card]
  obtain ⟨k,hk⟩ := D.U_half_odd
  rcases D.U_card with hU | hU <;> rw [hF] at hU <;>
    rcases hmod with hmod | hmod <;> omega

/-- An automorphism with square one fixing the supplied cubic lies in the
actual inner subgroup. The identity is allowed. -/
theorem square_one_cubic_fixer_inner {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hF : Nat.card F = p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (a : MulAut PSL(2,F)) (ha : a ^ 2 = 1)
    (x : PSL(2,F)) (hx : orderOf x = 3) (hfix : a x = x) :
    a ∈ MulAut.innerSubgroup PSL(2,F) := by
  have hlarge : 3 < Nat.card F := by have := Nat.mod_le p 24; omega
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p,1,Fact.out,hp,by decide,by simpa using hF⟩
  let f := pgl2InnerAutPSL2 F hodd hlarge
  obtain ⟨b,hb⟩ := Theory.PSL2.prime_card_pgl_coverage F hF hodd hlarge a
  have hb2 : b ^ 2 = 1 := (pgl2InnerAutPSL2_injective F hodd hlarge) (by
    rw [map_pow,hb,ha,map_one])
  by_cases hi : b ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  · obtain ⟨y,rfl⟩ := hi
    exact ⟨y,(pgl2InnerAutPSL2_toPGL F hodd hlarge y).symm.trans hb⟩
  have hb1 : b ≠ 1 := fun he => hi (he ▸ one_mem _)
  have hcent : Matrix.ProjectiveSpecialLinearGroup.toPGL x ∈
      centralizer ({b} : Set (PGL2 F)) := by
    rw [mem_centralizer_singleton_iff]
    have hh := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hfix
    rw [←hb,toPGL_pgl2InnerAutPSL2_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hthree : 3 ∣ Nat.card (centralizer ({b} : Set (PGL2 F))) := by
    let c : centralizer ({b} : Set (PGL2 F)) :=
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL x,hcent⟩
    have hc : orderOf c = 3 := by
      rw [←orderOf_injective (centralizer ({b} : Set (PGL2 F))).subtype
        Subtype.val_injective]
      change orderOf (Matrix.ProjectiveSpecialLinearGroup.toPGL x) = 3
      rw [orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,hx]
    exact hc ▸ orderOf_dvd_natCard c
  exact (outer_centralizer_not_three_dvd hp hF hmod b ⟨hb1,hb2⟩ hi hthree).elim

/-- Every elementary two-subgroup fixing an actual cubic pointwise lies
in the inner automorphism subgroup, without a nontriviality hypothesis. -/
theorem elementary_cubic_fixer_inner {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hF : Nat.card F = p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (A : Subgroup (MulAut PSL(2,F))) [IsElementaryAbelian 2 A]
    (x : PSL(2,F)) (hx : orderOf x = 3) (hfix : ∀ a ∈ A, a x = x) :
    A ≤ MulAut.innerSubgroup PSL(2,F) := by
  intro a ha
  exact square_one_cubic_fixer_inner hp hF hmod a
    (elemPow_eq_one_of_isElementaryAbelian a ha) x hx (hfix a ha)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.CubicFixer
