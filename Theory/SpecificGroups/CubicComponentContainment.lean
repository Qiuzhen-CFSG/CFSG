module
public import Theory.GroupTheory.CComponent.FullRankOuterAction
public import Theory.GroupTheory.TwoPerfectCubicKernel
public import Theory.SpecificGroups.G2.CubicFieldActors
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic

/-!
# Cubic containment in characteristic-two rank-two components

Let C be a normal C-component in a finite group of three-rank at most two.
If C/O₂(C) is G₂(q) or Sp₄(q), for even q > 2, every order-three element
of the ambient group belongs to C. The actual quotient action has rank at
most two: its kernel modulo the ambient two-core has order prime to three.
After transport through the model isomorphism, the fixed-field elementary
nine forces every cubic actor to be inner. Full-rank absorption puts it in C.

Consequently C contains every two-perfect A with |A/O₂(A)| = 3. Otherwise
the quotient action of A on G/C has two-group kernel, contradicting an
order-three element in A. Neither the two-core extension nor the ambient
action is assumed split. The original local applications are in
OriginalComponentStatement.RankTwoContainment.

Source: Aschbacher–Smith A.3.18, pp.51–53, used in the outside-component
branch of 14.7.41, p.1061, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.CubicComponentContainment

private theorem cubic_mem_of_full_rank_model
    {D X : Type*} [Group D] [Finite D] [Group X]
    (C : Subgroup D) [C.Normal] (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* X) (hzX : center X = ⊥)
    (hrX : 2 ≤ primeRank 3 X) (hrD : primeRank 3 D ≤ 2)
    (hinner : ∀ (B : Subgroup (MulAut X)), MulAut.innerSubgroup X ≤ B →
      primeRank 3 B ≤ 2 → ∀ a ∈ B, (∃ m : ℕ, a ^ (3^m) = 1) →
        a ∈ MulAut.innerSubgroup X)
    (x : D) (hx : orderOf x = 3) : x ∈ C := by
  let : Finite X := Finite.of_equiv (C ⧸ pCore 2 C) e.toEquiv
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center X at hh
    rw [hzX,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hzc : Nat.Coprime 3 (Nat.card (center (C ⧸ pCore 2 C))) := by
    rw [hz,card_bot]
    exact Nat.coprime_one_right _
  have hrC : 2 ≤ primeRank 3 C := by
    rw [←primeRank_congr 3 e,
      primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hrX
    exact hrX
  let a := normalQuotientAction C (pCore 2 C)
  let f := (MulAut.congr e).toMonoidHom.comp a
  have hr : primeRank 3 f.range ≤ 2 := by
    have hh := CComponentPrimeRank.quotientAction_rank_le_two C hC hzc hrC hrD (by decide)
    rw [show f.range = a.range.map (MulAut.congr e).toMonoidHom from MonoidHom.range_comp _ _]
    rw [←primeRank_congr 3 (a.range.equivMapOfInjective
      (MulAut.congr e).toMonoidHom (MulAut.congr e).injective)]
    exact hh
  have hi : MulAut.innerSubgroup X ≤ f.range := by
    rintro _ ⟨y,rfl⟩
    obtain ⟨c,hc⟩ := QuotientGroup.mk'_surjective (pCore 2 C) (e.symm y)
    refine ⟨c,?_⟩
    change MulAut.congr e (normalQuotientAction C (pCore 2 C) (c : D)) = _
    rw [normalQuotientAction_inner,MulAut.congr_conj,hc,e.apply_symm_apply]
  have hfx := hinner f.range hi hr (f x) ⟨x,rfl⟩ ⟨1,by
    rw [pow_one,←map_pow,←hx,pow_orderOf_eq_one,map_one]⟩
  have hax : a x ∈ MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
    rw [←MulAut.map_innerSubgroup_congr e] at hfx
    exact (mem_map_iff_mem (MulAut.congr e).injective).mp hfx
  by_contra hout
  exact CComponentPrimeRank.quotientAction_not_inner_of_outside C hC hzc hrC hrD
    (by decide) x hx hout hax

private theorem twoPerfect_cubic_le_of_cubic_mem
    {D : Type*} [Group D] [Finite D] (A C : Subgroup D) [C.Normal]
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hm : ∀ x : D, orderOf x = 3 → x ∈ C) : A ≤ C := by
  by_contra hout
  let f := (QuotientGroup.mk' C).comp A.subtype
  have hf : f ≠ 1 := by
    intro he
    apply hout
    intro a ha
    exact (QuotientGroup.eq_one_iff a).mp (DFunLike.congr_fun he (⟨a,ha⟩ : A))
  have hk := f.kernel_isTwoGroup_of_twoPerfect_cubic hp hc hf
  have hd : 3 ∣ Nat.card A := by
    have hh := card_quotient_dvd_card (pCore 2 A)
    rwa [hc] at hh
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hxD : orderOf (x : D) = 3 := (Subgroup.orderOf_coe x).trans hx
  have hxk : x ∈ f.ker := (QuotientGroup.eq_one_iff (x : D)).mpr (hm x hxD)
  have hh := hk.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x,hxk⟩ : f.ker)
  rw [Subgroup.orderOf_mk,hx] at hh
  norm_num at hh

variable {D : Type*} [Group D] [Finite D]
  {E : Type*} [Field E] [Finite E] [CharP E 2]

/-- A normal G₂(q) component absorbs every two-perfect cubic extension. -/
theorem gTwo_twoPerfect_cubic_le
    (A C : Subgroup D) [C.Normal] (hC : C.IsCComponent)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hr : primeRank 3 D ≤ 2) (hE : 2 < Nat.card E)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.G2.Model E) : A ≤ C := by
  apply twoPerfect_cubic_le_of_cubic_mem A C hp hc
  exact cubic_mem_of_full_rank_model C hC e
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hE)
    Atlas.G2.CubicFieldActors.cubic_rank hr
    (Atlas.G2.CubicFieldActors.cubic_primePower_actor_inner hE)

/-- A normal Sp₄(q) component absorbs every two-perfect cubic extension. -/
theorem symplecticFour_twoPerfect_cubic_le
    (A C : Subgroup D) [C.Normal] (hC : C.IsCComponent)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hr : primeRank 3 D ≤ 2) (hE : 2 < Nat.card E)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.symplecticGroup (Fin 2) E) : A ≤ C := by
  apply twoPerfect_cubic_le_of_cubic_mem A C hp hc
  exact cubic_mem_of_full_rank_model C hC e
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
    Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_rank hr
    (Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_primePower_actor_inner hE)

end Theory.SpecificGroups.CubicComponentContainment
