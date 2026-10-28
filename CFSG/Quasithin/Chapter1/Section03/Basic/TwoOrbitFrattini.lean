module
public import CFSG.Quasithin.Chapter1.Section03.Basic.FrattiniAction
public import Theory.GroupAction.TwoOrbitInnerAction
public import Theory.GroupAction.IrreducibleNormalIntersection

/-!
# Irreducible odd action on a pair of components

Squares of normalizer elements fix each component of an orbit of length two.
If the outer group is abelian, their commutators with the odd subgroup act
inner on both factors. Irreducibility rules out a proper invariant intersection:
the resulting Frattini action would consist of commuting involutions and hence
have cyclic irreducible sections. A two-group outer group instead gives inner
action directly by coprimality. No Sylow hypothesis on the actor is required.

This supplies the inner-action step of Aschbacher--Smith, 13.1.12(3), printed
p.874, using the Frattini action argument of 1.3.2(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsNormalizerFrattiniIrreducible.le_normal_of_square_displacements
    {P N : Subgroup G} [N.Normal]
    (hirr : IsNormalizerFrattiniIrreducible P) {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hdisp : ∀ s : normalizer (P : Set G), ∀ x : P,
      (s : G)^2 * (x : G) * ((s : G)^2)⁻¹ * (x : G)⁻¹ ∈ N) : P ≤ N := by
  rcases hirr.invariant_le_frattini_or_eq (N.subgroupOf P) (by
    intro s d hd
    exact (inferInstance : N.Normal).conj_mem d hd s) with hk | hk
  · let : Fact (IsPGroup p P) := ⟨hP⟩
    let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
    let _ := conjMulDistribMulActionOfLeNormalizer (normalizer (P : Set G)) P le_rfl
    let f := frattiniConjugationHom (normalizer (P : Set G)) P le_rfl
    have hpow : ∀ s, f s ^ 2 = 1 := by
      intro s
      rw [← map_pow]
      apply MulEquiv.ext
      intro v
      induction v using QuotientGroup.induction_on with | H x =>
        change quotientAut (frattini P)
          (MulDistribMulAction.toMulAut (normalizer (P : Set G)) P (s ^ 2))
          (QuotientGroup.mk' (frattini P) x) = QuotientGroup.mk' (frattini P) x
        rw [quotientAut_apply_mk]
        apply QuotientGroup.eq_iff_div_mem.mpr
        apply hk
        change ((s : G)^2 * (x : G) * ((s : G)^2)⁻¹) / (x : G) ∈ N
        simpa only [div_eq_mul_inv] using hdisp s x
    exact (OddInvolutionFrattini.noncyclic_frattini_quotient hnc
      (CFSG.Quasithin.Chapter1.XiAction.isCyclic_of_irreducible_involutive f hpow hirr)).elim
  · intro x hx
    exact (show (⟨x,hx⟩ : P) ∈ N.subgroupOf P from hk ▸ mem_top _)

private theorem square_displacement_mem_inner (B : Subgroup G)
    [IsMulCommutative (MulAut.Outer B)] (hi : (normalizer (B : Set G)).index = 2)
    {P : Subgroup G} {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (ho : Odd p)
    (s : G) (x : P) : s^2 * (x : G) * (s^2)⁻¹ * (x : G)⁻¹ ∈
      B ⊔ centralizer (B : Set G) := by
  let N := normalizer (B : Set G)
  let a : N := ⟨s^2,N.sq_mem_of_index_two hi s⟩
  let b : N := ⟨x,odd_pGroup_le_index_two_source P N hP ho hi x.property⟩
  let f : N →* MulAut.Outer B :=
    (QuotientGroup.mk' (MulAut.innerSubgroup B)).comp B.normalizerMonoidHom
  have hzero : f (a*b*a⁻¹*b⁻¹) = 1 := by
    rw [map_mul,map_mul,map_mul,map_inv,map_inv,mul_comm (f a) (f b),
      mul_inv_cancel_right,mul_inv_cancel]
  have hin : NormalizerAction.quotient B (a*b*a⁻¹*b⁻¹) ∈
      NormalizerAction.componentImage B := by
    apply (NormalizerAction.action_mem_inner_iff B _).mp
    exact (QuotientGroup.eq_one_iff _).mp hzero
  obtain ⟨y,hy,he⟩ := hin
  have hc : (y : G)⁻¹ * (s^2 * (x : G) * (s^2)⁻¹ * (x : G)⁻¹) ∈
      centralizer (B : Set G) := by
    apply (NormalizerAction.quotient_eq_one_iff B (y⁻¹ * (a*b*a⁻¹*b⁻¹))).mp
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hh := (B ⊔ centralizer (B : Set G)).mul_mem (mem_sup_left hy) (mem_sup_right hc)
  change (y : G) * ((y : G)⁻¹ * _) ∈ _ at hh
  simpa only [mul_inv_cancel_left] using hh

theorem IsNormalizerFrattiniIrreducible.inner_on_two_component_orbit
    {p : ℕ} [Fact p.Prime] (B P A : Subgroup G)
    (hirr : IsNormalizerFrattiniIrreducible P) (hP : IsPGroup p P)
    (ho : Odd p) (hnc : ¬ IsCyclic P) (hB : IsComponent G B)
    (hi : (normalizer (B : Set G)).index = 2)
    (hout : IsMulCommutative (MulAut.Outer B) ∨ IsPGroup 2 (MulAut.Outer B))
    [(componentOrbit B A).Normal] :
    P ≤ componentOrbit B A ⊔ centralizer (componentOrbit B A : Set G) := by
  have hn : normalizer (B : Set G) ≠ ⊤ := by intro he; simp [he] at hi
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hn)
  let C := B.map (MulAut.conj g).toMonoidHom
  have hBC : B ≠ C := by
    intro he
    exact hg.2 (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hcomm : B ≤ centralizer (C : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hB.commutator_eq_bot_of_ne (hB.map_conj g) hBC)
  have hCi : (normalizer (C : Set G)).index = 2 := by
    dsimp only [C]
    rw [← map_equiv_normalizer_eq,index_map_of_bijective (MulAut.conj g).bijective]
    exact hi
  let e : B ≃* C := B.equivMapOfInjective _ (MulAut.conj g).injective
  let eo := MulAut.outerCongr e
  have hpair := orbit_eq_pair_of_normal_index_two_source B A hi g hg.2
  rcases hout with hab | htwo
  · let := hab
    let : IsMulCommutative (MulAut.Outer C) := ⟨⟨fun x y => by
      apply eo.symm.injective
      rw [map_mul,map_mul,mul_comm]⟩⟩
    apply hirr.le_normal_of_square_displacements hP hnc
    intro s x
    rw [hpair]
    apply inner_sup_of_commuting_factors_source B C hcomm
    exact ⟨square_displacement_mem_inner B hi hP ho s x,
      square_displacement_mem_inner C hCi hP ho s x⟩
  · have hleft := inner_of_outer_two_group_source B P hP ho
      (odd_pGroup_le_index_two_source P _ hP ho hi) htwo
    have hright := inner_of_outer_two_group_source C P hP ho
      (odd_pGroup_le_index_two_source P _ hP ho hCi) (htwo.of_equiv eo)
    rw [hpair]
    exact (le_inf hleft hright).trans (inner_sup_of_commuting_factors_source B C hcomm)
end Subgroup

