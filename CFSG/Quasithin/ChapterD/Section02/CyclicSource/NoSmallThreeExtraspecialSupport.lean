module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeExtraspecialCenter
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Separation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The full six-dimensional module in the extraspecial source branch

A faithful extraspecial group of order 27 is irreducible on its binary
six-dimensional support; its center therefore has the same support.
The characteristic cubic center is central in G: an inverting starred
involution would force its support to have dimension four by D.2.26.
On the two-dimensional displacement of a starred involution, a central
cubic acts either trivially or without fixed vectors. This separates the
cubic support and its fixed complement, so source indecomposability makes
the support the whole original module.
Source: Aschbacher–Smith, D.2.26–29 and the final paragraph, pp.191–192.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

theorem extraspecial_center_support_eq (hf : Function.Injective ρ)
    (F : Subgroup G) [IsExtraspecial 3 F] (hcard : Nat.card F = 27)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ F) = 6) :
    subspaceCommutator ρ ⊤ ((center F).map F.subtype) = subspaceCommutator ρ ⊤ F := by
  let U := subspaceCommutator ρ ⊤ F
  let Z := (center F).map F.subtype
  have hZF : Z ≤ F := by rintro _ ⟨z,_,rfl⟩; exact z.property
  have hUF : F ≤ subspaceStabilizer ρ U := subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) F.le_normalizer
  let τ : Representation (ZMod 2) F U :=
    (stabilizerRepresentation ρ U).comp (inclusion hUF)
  have hcompF : IsCompl (fixedSpace ρ F) U := by
    simpa only [U,RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ)
        (show Odd (Nat.card F) by rw [hcard]; decide))
  have hτ : Function.Injective τ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply hf
    ext v
    obtain ⟨c,hc,u,hu,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace ρ F ⊔ U by rw [hcompF.sup_eq_top]; trivial)
    have hau : ρ (a : G) u = u :=
      congrArg (fun x : U => x.val) (LinearMap.congr_fun ha ⟨u,hu⟩)
    have hac : ρ (a : G) c = c := hc a
    simp only [Subgroup.coe_one,map_one,Module.End.one_apply,map_add,hac,hau]
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center F) 3
    (by rw [IsExtraspecial.center_order_p 3 F])
  have hzc : orderOf (z : F) = 3 := (orderOf_coe z).trans hz
  have hfree := RankTwo.ExtraspecialModel.fixed_free_of_faithful_six τ hτ hcard hdim
    (z : F) hzc z.property
  have hZU : subspaceCommutator ρ ⊤ Z ≤ U := by
    apply Submodule.span_mono
    rintro _ ⟨x,hx,v,hv,rfl⟩
    exact ⟨x,hZF hx,v,hv,rfl⟩
  have hcardZ : Nat.card Z = 3 := by
    rw [card_map_of_injective F.subtype_injective,IsExtraspecial.center_order_p 3 F]
  have hcompZ : IsCompl (fixedSpace ρ Z) (subspaceCommutator ρ ⊤ Z) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ)
        (show Odd (Nat.card Z) by rw [hcardZ]; decide))
  apply le_antisymm hZU
  intro u hu
  obtain ⟨c,hc,s,hs,he⟩ := Submodule.mem_sup.mp
    (show u ∈ fixedSpace ρ Z ⊔ subspaceCommutator ρ ⊤ Z by rw [hcompZ.sup_eq_top]; trivial)
  have hcU : c ∈ U := by
    have hh := U.sub_mem hu (hZU hs)
    simpa only [←he,add_sub_cancel_right] using hh
  have hc0 : c = 0 := by
    have hh : τ (z : F) (⟨c,hcU⟩ : U) = ⟨c,hcU⟩ := by
      apply Subtype.ext
      exact hc ⟨((z:F):G),mem_map_of_mem F.subtype z.property⟩
    exact congrArg (fun x : U => x.val) (hfree ⟨c,hcU⟩ hh)
  rw [←he,hc0,zero_add]
  exact hs
theorem CoreHypotheses.normal_cubic_six_support_central
    {ρ : Representation (ZMod 2) G V} (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ pCore 3 G) (hcard : Nat.card Z = 3)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 6) :
    Z ≤ center G := by
  classical
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (by rw [hcard])
  have hz3 : orderOf (z : G) = 3 := (orderOf_coe z).trans hz
  have hzgen : zpowers (z : G) = Z := eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    (by rw [Nat.card_zpowers,hz3,hcard])
  have hzpow : (z : G)^2 = (z : G)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←pow_succ]
    simpa only [hz3] using pow_orderOf_eq_one (z : G)
  have hall : smallSupportInvolutions ρ ⊆ centralizer (Z : Set G) := by
    intro t ht
    have hzt : Commute t (z : G) := by
      have hconj : t * (z:G) * t⁻¹ ∈ zpowers (z:G) :=
        hzgen.symm ▸ (inferInstance : Z.Normal).conj_mem z z.property t
      rw [mem_zpowers_iff_mem_range_orderOf,hz3] at hconj
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hconj
      have hn3 := Finset.mem_range.mp hn
      interval_cases n
      · have hzne : (z:G) ≠ 1 := by intro he; simp [he] at hz3
        exact (hzne ((MulAut.conj t).injective (by simpa using he.symm))).elim
      · exact mul_inv_eq_iff_eq_mul.mp (by simpa only [pow_one] using he.symm)
      · have hinv : t * (z:G) * t⁻¹ = (z:G)⁻¹ := he.symm.trans hzpow
        have hh := h.inverted_threeCore_support hq hNo ht (hZ z.property)
          (by intro he; simp [he] at hz3) hinv
        rw [hzgen,hdim] at hh
        omega
    change t ∈ centralizer (Z : Set G)
    rw [←hzgen,mem_centralizer_iff]
    rintro a ⟨n,rfl⟩
    exact (hzt.zpow_right n).eq.symm
  have htop : (⊤ : Subgroup G) ≤ centralizer (Z : Set G) := by
    rw [←h.smallSupport_generated]
    exact (closure_le _).mpr hall
  intro z hz
  rw [mem_center_iff]
  intro g
  exact (mem_centralizer_iff.mp (htop (mem_top g)) z hz).symm

end CFSG.Quasithin.ChapterD.CyclicSource

namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem central_cubic_rank_two_dichotomy
    (Z : Subgroup G) (hZ : Z ≤ center G) (hc : Nat.card Z = 3)
    (t : G) (ht : fixedCodim ρ (zpowers t) = 2) :
    subspaceCommutator ρ ⊤ Z ≤ fixedSpace ρ (zpowers t) ∨
      fixedSpace ρ Z ≤ fixedSpace ρ (zpowers t) := by
  let D := (ρ t - LinearMap.id).range
  have hdim : Module.finrank (ZMod 2) D = 2 :=
    (fixedCodim_zpowers_eq_displacement_rank ρ t).symm.trans ht
  have hcomm (z : G) (hz : z ∈ Z) (v : V) : ρ t (ρ z v) = ρ z (ρ t v) := by
    simp only [←Module.End.mul_apply,←map_mul,mem_center_iff.mp (hZ hz) t]
  have hZD : Z ≤ subspaceStabilizer ρ D := by
    apply le_subspaceStabilizer
    intro z hz v hv
    obtain ⟨w,rfl⟩ := hv
    refine ⟨ρ z w,?_⟩
    change ρ t (ρ z w) - ρ z w = ρ z (ρ t w - w)
    rw [map_sub,hcomm z hz]
  let τ : Representation (ZMod 2) Z D :=
    (stabilizerRepresentation ρ D).comp (inclusion hZD)
  have hp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  have hdvd : 2 ∣ fixedCodim τ ⊤ := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_three] using
      orderOf_two_dvd_fixedCodim_of_isPGroup τ (by decide : Nat.Prime 3) (by decide) ⊤
        (hp.to_subgroup ⊤)
  have hadd := fixedCodim_add_finrank τ ⊤
  rw [hdim] at hadd
  have hcases : fixedCodim τ ⊤ = 0 ∨ fixedCodim τ ⊤ = 2 := by omega
  rcases hcases with hzero | htwo
  · left
    have hfix : fixedSpace τ ⊤ = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    have hdfix (z : G) (hz : z ∈ Z) (v : V) : ρ z (ρ t v - v) = ρ t v - v := by
      let d : D := ⟨ρ t v-v,⟨v,rfl⟩⟩
      have hh : d ∈ fixedSpace τ ⊤ := hfix ▸ Submodule.mem_top
      exact congrArg (fun x : D => x.val) (hh ⟨⟨z,hz⟩,mem_top _⟩)
    apply Submodule.span_le.mpr
    rintro _ ⟨z,hz,v,_,rfl⟩
    change ρ z v-v ∈ fixedSpace ρ (zpowers t)
    rw [mem_fixedSpace_zpowers_iff]
    apply sub_eq_zero.mp
    calc
      ρ t (ρ z v-v) - (ρ z v-v) = ρ z (ρ t v-v) - (ρ t v-v) := by
        rw [map_sub,map_sub,hcomm z hz]
        abel
      _ = 0 := by rw [hdfix z hz,sub_self]
  · right
    have hfix : fixedSpace τ ⊤ = ⊥ := (Submodule.finrank_eq_zero).mp (by omega)
    intro v hv
    rw [mem_fixedSpace_zpowers_iff]
    apply sub_eq_zero.mp
    let d : D := ⟨ρ t v-v,⟨v,rfl⟩⟩
    have hh : d ∈ fixedSpace τ ⊤ := by
      intro z
      apply Subtype.ext
      change ρ (z.val : G) (ρ t v-v) = ρ t v-v
      have hvz : ρ (z.val : G) v = v := hv z.val
      rw [map_sub,←hcomm z.val z.val.property,hvz]
    have hd0 : d = 0 := by simpa only [hfix,Submodule.mem_bot] using hh
    exact congrArg (fun x : D => x.val) hd0
theorem Hypotheses.central_cubic_six_full [Finite G]
    {ρ : Representation (ZMod 2) G V} (h : Hypotheses ρ) (hq : cubicRatio ρ = 2)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ center G) (hc : Nat.card Z = 3)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 6) :
    subspaceCommutator ρ ⊤ Z = ⊤ ∧ fixedSpace ρ Z = ⊥ ∧
      Module.finrank (ZMod 2) V = 6 := by
  let : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have hcompl : IsCompl (subspaceCommutator ρ ⊤ Z) (fixedSpace ρ Z) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ)
        (show Odd (Nat.card Z) by rw [hc]; decide)).symm
  have hstable := subspaceCommutator_invariant_normalizer ρ
    (X := Z) (A := ⊤) (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
    le_normalizer_of_normal
  obtain ⟨hfull,hfix⟩ := support_eq_top_of_starred_dichotomy ρ h.generated h.indecomposable
    h.fixedSpace_eq_bot _ _ hcompl
    (fun g w hw => (hstable (mem_top g) w).2 hw)
    (fun g w hw => (fixedSpace_stable_of_normal ρ Z (mem_top g) w).2 hw)
    (by intro he; rw [he,finrank_bot] at hd; omega) (by
      intro A hA
      obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
      have hcodim : fixedCodim ρ (zpowers t) = 2 := by
        rw [he]
        exact_mod_cast (starred_codimension ρ hA (h.rank_one A hA)).trans hq
      simpa only [he] using central_cubic_rank_two_dichotomy ρ Z hZ hc t hcodim)
  refine ⟨hfull,hfix,?_⟩
  have hfull' : subspaceCommutator ρ ⊤ Z = ⊤ := hfull
  rw [hfull',finrank_top] at hd
  exact hd

end CFSG.Quasithin.ChapterD.CyclicSource


namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- All the field-extension inputs on the unchanged source module. -/
theorem Hypotheses.extraspecial_six_space
    (h : Hypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (t : G) (ht : t ∈ smallSupportInvolutions ρ)
    (hF : IsExtraspecial 3 (⁅pCore 3 G,zpowers t⁆ : Subgroup G))
    (hc : Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 27)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 3 G,zpowers t⁆) = 6) :
    let Z := (center (⁅pCore 3 G,zpowers t⁆ : Subgroup G)).map
      (⁅pCore 3 G,zpowers t⁆ : Subgroup G).subtype
    Nat.card Z = 3 ∧ Z ≤ center G ∧ subspaceCommutator ρ ⊤ Z = ⊤ ∧
      fixedSpace ρ Z = ⊥ ∧ Module.finrank (ZMod 2) V = 6 := by
  let F := ⁅pCore 3 G,zpowers t⁆
  let Z := (center F).map F.subtype
  let : IsExtraspecial 3 F := hF
  let : Z.Normal := h.toCoreHypotheses.extraspecial_center_normal hH f honto hfive t ht.1 hF
  have hZR : Z ≤ pCore 3 G := by
    rintro _ ⟨z,_,rfl⟩
    exact commutator_le_left (pCore 3 G) (zpowers t) z.property
  have hZcard : Nat.card Z = 3 := by
    rw [card_map_of_injective F.subtype_injective,IsExtraspecial.center_order_p 3 F]
  have hZdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 6 := by
    rw [extraspecial_center_support_eq ρ h.faithful F hc hd]
    exact hd
  have hZcentral := h.toCoreHypotheses.normal_cubic_six_support_central hq hNo Z hZR hZcard hZdim
  exact ⟨hZcard,hZcentral,h.central_cubic_six_full hq Z hZcentral hZcard hZdim⟩
end CFSG.Quasithin.ChapterD.CyclicSource
