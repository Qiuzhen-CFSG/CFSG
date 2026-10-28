module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.ActionFacts
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.Contracts
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The marked local symmetric-three quotient

The literal I₂-action on V₂ has full automorphism image. Indeed, its point
core has nontrivial two-group image, while its two-residual contains an
actor fixing no nonidentity plane element. The image therefore has even
order and cannot be a two-group; its order divides six, so it is all S₃.
The known action kernel is the actual O₂(I₂), giving the quotient
isomorphism. Transport of O²(I₂) identifies the image of L₂ with the cubic
subgroup. Conjugating the coordinates puts the order-two point-core image
at the specified inverter and preserves the characteristic cubic subgroup.

This constructs the three fields of `QuotientMarking` from `NaturalSetup`
and the earlier local identities in `LocalData`. No quotient marking or
coordinates on V/V₂ are assumed. Compatible coordinates on that latter
module are a separate construction retained by the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4(1),(2),(5),(6), printed p.916, and the local action used in the proof
of 13.8.6, printed p.948.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking.GroupQuotient
open EarlierCore RankDoubling.SourceAction InvertedCubicTensor
noncomputable section

private theorem two_subgroup_card {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A = 6) (P : Subgroup A) (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    Nat.card P = 2 := by
  have hdiv : Nat.card P ∣ 6 := hc ▸ P.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card P) 3 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hdiv2 : Nat.card P ∣ 2 := hcop.dvd_mul_right.mp hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h1 | h2
  · exact (hne (Subgroup.card_eq_one.mp h1)).elim
  · exact h2

private theorem three_residual : pResidual 2 S₃ = zpowers cubic := by
  rw [Equiv.Perm.twoResidual_eq_alternating]
  apply le_antisymm
  · have hc : ∀ g : S₃, g ∈ alternatingGroup (Fin 3) →
        g = 1 ∨ g = cubic ∨ g = cubic * cubic := by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    intro g hg
    rcases hc g hg with rfl | rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
    · exact mul_mem (mem_zpowers _) (mem_zpowers _)
  · apply zpowers_le.mpr
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel

private theorem preserves_cubic (e : S₃ ≃* S₃) :
    (zpowers cubic).map e.toMonoidHom = zpowers cubic := by
  rw [← three_residual, map_pResidual]

private theorem mark_two_subgroup (P : Subgroup S₃) (hP : Nat.card P = 2) :
    ∃ e : S₃ ≃* S₃, P.map e.toMonoidHom = zpowers inverter ∧
      (zpowers cubic).map e.toMonoidHom = zpowers cubic := by
  have hne : P ≠ ⊥ := P.one_lt_card_iff_ne_bot.mp (by omega)
  obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ht1 : (t : S₃) ≠ 1 := by intro h; exact ht (Subtype.ext h)
  have ht2 : (t : S₃) ^ 2 = 1 := by
    have h := congrArg (fun x : P => (x : S₃)) (pow_card_eq_one' (x := t))
    simpa only [hP, Subgroup.coe_pow, Subgroup.coe_one] using h
  have hconj : ∀ t : S₃, t ≠ 1 → t ^ 2 = 1 → ∃ g : S₃, g * t * g⁻¹ = inverter := by
    decide +kernel
  obtain ⟨g, hg⟩ := hconj t ht1 ht2
  have hgen : P = zpowers (t : S₃) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr t.property) ?_).symm
    rw [hP, Nat.card_zpowers, orderOf_eq_prime ht2 ht1]
  refine ⟨MulAut.conj g, ?_, preserves_cubic _⟩
  rw [hgen, MonoidHom.map_zpowers]
  change zpowers (g * (t : S₃) * g⁻¹) = _
  rw [hg]

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H L V V₁ V₂ V₃ : Subgroup G}
  (s : NaturalSetup T L V V₁ V₂ V₃)
  (d : LocalData H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂))

include d

omit [Finite G] in
private theorem residual_inside :
    (localResidual L V₂).subgroupOf (localI L V₁ V₂) = pResidual 2 (localI L V₁ V₂) := by
  apply map_subtype_inj.mp
  rw [map_subgroupOf_eq_of_le (show localResidual L V₂ ≤ localI L V₁ V₂ from le_sup_right)]
  exact d.residual

private theorem point_image_ne_bot :
    (((normalizer (V₁ : Set G)).pCoreIn 2).subgroupOf (localI L V₁ V₂)).map
      (planeAction s) ≠ ⊥ := by
  intro hb
  apply point_core_not_le_centralizer s d
  intro x hx
  have hxI : x ∈ localI L V₁ V₂ :=
    (le_sup_left : (normalizer (V₁ : Set G)).pCoreIn 2 ≤ localI L V₁ V₂) hx
  have hk := (Subgroup.map_eq_bot_iff _).mp hb (show (⟨x, hxI⟩ : localI L V₁ V₂) ∈
    ((normalizer (V₁ : Set G)).pCoreIn 2).subgroupOf (localI L V₁ V₂) from hx)
  change inclusion s.localI_le_plane_normalizer ⟨x, hxI⟩ ∈ V₂.normalizerMonoidHom.ker at hk
  rw [normalizerMonoidHom_ker] at hk
  exact hk

private theorem range_not_two : ¬ IsPGroup 2 (planeAction s).range := by
  intro hp
  have hk : pResidual 2 (localI L V₁ V₂) ≤ (planeAction s).ker :=
    sInf_le ⟨inferInstance, hp.of_equiv (QuotientGroup.quotientKerEquivRange _).symm⟩
  obtain ⟨l, hl⟩ := exists_plane_fixedFree_actor s
  let i : localI L V₁ V₂ := inclusion le_sup_right l
  have hi : i ∈ pResidual 2 (localI L V₁ V₂) := by
    rw [← residual_inside d]
    exact l.property
  have he := MonoidHom.mem_ker.mp (hk hi)
  let : Nontrivial V₂ := Finite.one_lt_card_iff_nontrivial.mp (by rw [plane_card s]; decide)
  obtain ⟨v, hv⟩ := exists_ne (1 : V₂)
  exact hv (hl v (by change planeAction s i v = v; rw [he]; rfl))

variable [IsElementaryAbelian 2 V]

/-- The literal local group induces the full automorphism group of the plane. -/
theorem planeAction_surjective : Function.Surjective (planeAction s) := by
  let : IsKleinFour V₂ := plane_isKleinFour s
  let P := (((normalizer (V₁ : Set G)).pCoreIn 2).subgroupOf (localI L V₁ V₂)).map
    (planeAction s)
  have hp : IsPGroup 2 P := ((isPGroup_pCoreIn 2 _).comap_subtype).map _
  have hP : Nat.card P = 2 :=
    two_subgroup_card (IsKleinFour.card_mulAut V₂) P hp (point_image_ne_bot s d)
  have hle : P ≤ (planeAction s).range := map_le_range _ _
  have htwo : 2 ∣ Nat.card (planeAction s).range := hP ▸ card_dvd_of_le hle
  have hdiv : Nat.card (planeAction s).range ∣ 6 :=
    IsKleinFour.card_mulAut V₂ ▸ (planeAction s).range.card_subgroup_dvd_card
  have hbound := Nat.le_of_dvd (by decide : 0 < 6) hdiv
  have hc : Nat.card (planeAction s).range = 6 := by
    interval_cases h : Nat.card (planeAction s).range <;> norm_num at *
    exact (range_not_two s d (IsPGroup.of_card (n := 1) (by simpa using h))).elim
  apply MonoidHom.range_eq_top.mp
  exact ((planeAction s).range.card_eq_iff_eq_top).mp
    (hc.trans (IsKleinFour.card_mulAut V₂).symm)

include s in
/-- Construct the literal I₂/O₂(I₂) isomorphism, with L₂ mapped to the
cubic subgroup and the point core mapped to the specified inverter subgroup. -/
theorem quotientMarking_nonempty : Nonempty (QuotientMarking L V₁ V₂) := by
  let : IsKleinFour V₂ := plane_isKleinFour s
  let a := IsKleinFour.autEquivPermThree V₂
  let φ : localI L V₁ V₂ →* S₃ := a.toMonoidHom.comp (planeAction s)
  have hφ : Function.Surjective φ := a.surjective.comp (planeAction_surjective s d)
  have hk : φ.ker = pCore 2 (localI L V₁ V₂) :=
    (MonoidHom.ker_comp_of_injective (planeAction s) a.toMonoidHom a.injective).trans
      (planeAction_ker s d)
  let e₀ : (localI L V₁ V₂ ⧸ pCore 2 (localI L V₁ V₂)) ≃* S₃ :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have he₀ : e₀.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localI L V₁ V₂))) = φ := by
    ext i
    rfl
  have hr : ((localResidual L V₂).subgroupOf (localI L V₁ V₂)).map φ = zpowers cubic := by
    rw [residual_inside d, map_pResidual_of_surjective 2 φ hφ, three_residual]
  let P := (((normalizer (V₁ : Set G)).pCoreIn 2).subgroupOf (localI L V₁ V₂)).map φ
  have hp : IsPGroup 2 P := ((isPGroup_pCoreIn 2 _).comap_subtype).map _
  have hne : P ≠ ⊥ := by
    intro hb
    apply point_image_ne_bot s d
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [Subgroup.map_bot, map_map]
    exact hb
  have hc : Nat.card S₃ = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  obtain ⟨e, heP, heC⟩ := mark_two_subgroup P (two_subgroup_card hc P hp hne)
  refine ⟨⟨e₀.trans e, ?_, ?_⟩⟩
  · change ((localResidual L V₂).subgroupOf (localI L V₁ V₂)).map
      (e.toMonoidHom.comp (e₀.toMonoidHom.comp (QuotientGroup.mk' _))) = _
    rw [he₀, ← map_map, hr, heC]
  · change (((normalizer (V₁ : Set G)).pCoreIn 2).subgroupOf (localI L V₁ V₂)).map
      (e.toMonoidHom.comp (e₀.toMonoidHom.comp (QuotientGroup.mk' _))) = _
    rw [he₀, ← map_map]
    exact heP

end
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking.GroupQuotient
