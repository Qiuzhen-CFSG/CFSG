module
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
/-!
# Binary cubic ratios for the actual PSL₂(25) actor

Every inner involution in PSL₂(25) inverts an element of order thirteen.
The binary order-thirteen displacement bound forces it to move at least
six dimensions in any faithful representation. Dihedral Sylow two-groups
bound every elementary actor rank by two, so its cubic ratio exceeds two.
No irreducibility or ambient outer-action hypothesis is needed.

Source: the inner-involution argument of Guralnick–Malle, Classification of
2F-modules I, Proposition 4.1, as used in Aschbacher–Smith K.2 and C.5.13,
printed pp.453 and163. The torus/fusion proof follows the checked source
`TwentyFive.InnerInvolutions`, here stated for the actual simple actor.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Theory.PSL2
private theorem model_inverts_thirteen {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 25)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (ht : orderOf t = 2) :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      orderOf x = 13 ∧ t * x * t⁻¹ = x⁻¹ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨S, w, _, hS, _, hwS, hw2, hwinv, _, _⟩ :=
    BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data
      (p := 5) (f := 2) (by simpa using hF)
  have hS13 : Nat.card S = 13 := by simpa [hF] using hS
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 13 (by rw [hS13])
  have hw1 : w ≠ 1 := fun hh => hwS (hh ▸ S.one_mem)
  have hw : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2) hw1
  obtain ⟨c, hc⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj w t hw ht)
  refine ⟨c * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * c⁻¹, ?_, ?_⟩
  · change orderOf (MulAut.conj c (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = 13
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  · rw [← hc]
    calc
      _ = c * (w * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * w⁻¹) * c⁻¹ := by group
      _ = c * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)⁻¹ * c⁻¹ := by rw [hwinv x x.property]
      _ = _ := by group

/-- Every faithful binary representation of the actual PSL₂(25) group has cubic ratio above two. -/
theorem two_lt_cubicRatio_of_twentyFive {G V F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hF : Nat.card F=25) (e : G ≃* PSL(2,F)) : 2 < cubicRatio ρ := by
  have hr : primeRank 2 G ≤ 2 := by
    rw [primeRank_equiv 2 e]
    let P : Sylow 2 PSL(2,F) := Classical.choice inferInstance
    have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩
    obtain ⟨n,_,⟨en⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
    rw [P.primeRank_eq,primeRank_equiv 2 en]
    exact dihedral_rank_le_two n
  by_contra hn
  obtain ⟨A,hA,_,hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp (le_of_not_gt hn)
  have hAr := hA.rank_le_of_primeRank_le hr
  obtain ⟨t,htA,ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let := hA.2
  have ht2 : orderOf t=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) ht
  obtain ⟨x,hx,hi⟩ := model_inverts_thirteen hF (e t) (e.orderOf_eq t |>.trans ht2)
  let y := e.symm x
  have hy : orderOf y=13 := (e.symm.orderOf_eq x).trans hx
  have hinv : t*y*t⁻¹=y⁻¹ := by
    apply e.injective
    simpa only [y,map_mul,map_inv,MulEquiv.apply_symm_apply] using hi
  have hc : orderOf (t*y*t⁻¹*y⁻¹)=13 := by
    rw [hinv,← mul_inv_rev,← pow_two,orderOf_inv]
    have ho : Odd (orderOf y) := by rw [hy]; decide
    rw [ho.coprime_two_right.orderOf_pow,hy]
  have hlo : 12 ≤ fixedCodim ρ (zpowers (t*y*t⁻¹*y⁻¹)) := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_thirteen] using
      prime_order_le_fixedCodim ρ hf (by decide : Nat.Prime 13) (by decide) _ hc
  have hup := fixedCodim_commutator_le_twice ρ t y
  have hfix := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr htA))
  have h1 := fixedCodim_add_finrank ρ (zpowers t)
  have h2 := fixedCodim_add_finrank ρ A
  omega

end Theory.PSL2
