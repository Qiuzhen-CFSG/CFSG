module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.PointAction
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.GroupTheory.PCoreSurjective

/-!
# The symmetric-five star quotient before module recognition

The two-group supplement extends an A₅ residual quotient only to A₅
or S₅. To exclude A₅, restrict the star map to the original L₁T.
Its two-group kernel and its S₃ core quotient force the image order to
be six times its two-core order. The ambient Sylow subgroup maps into
that image. Inside A₅ these conditions force orders twelve and two.
The central involution would make the image a two-group, a contradiction.
Thus the literal H/O₂(H) is S₅, without assuming any source datum.

The point action uses the independent universal Structural1222 input.
The residual alternative and the subsequent natural-module recognition
remain separate source obligations.

Source: Aschbacher–Smith, the final paragraph of the proof of 14.7.40,
printed p.1063, and the A₅ alternative of 14.7.52, printed p.1065.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- Count the actual point-parabolic image through any two-group kernel. -/
theorem point_image_ratio
    {A : Type*} [Group A] [Finite A]
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (f : B →* A) (hk : IsPGroup 2 f.ker) :
    Nat.card f.range = 6 * Nat.card (pCore 2 f.range) := by
  let g := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hgk : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  have hquot : Nat.card (B ⧸ pCore 2 B) = 6 := by
    rw [Nat.card_congr (pointQuotientEquiv h structural).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hquot, g.card_pCore_of_ker_isPGroup hg hgk] at hc
  have hc' := card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv] at hc'
  apply Nat.mul_left_cancel (Nat.card_pos (α := g.ker))
  nlinarith [hc, hc']

private theorem alternating_five_impossible
    (I : Subgroup (alternatingGroup (Fin 5)))
    (h4 : 4 ∣ Nat.card I)
    (hratio : Nat.card I = 6 * Nat.card (pCore 2 I)) : False := by
  have hd : Nat.card I ∣ 60 := by
    have he : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact he ▸ I.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := I)).exists_card_eq
  have hb := Nat.le_of_dvd (by decide : 0 < 60) hd
  have hnle : n ≤ 3 := by
    by_contra h
    have hp : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hn] at hratio
    norm_num at hp
    omega
  have hcards : Nat.card I = 12 ∧ Nat.card (pCore 2 I) = 2 := by
    interval_cases n <;> norm_num at hn <;> simp_all
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pCore 2 I) 2
    (by simp [hcards.2])
  let y : alternatingGroup (Fin 5) := x.val.val
  have hy : orderOf y = 2 := by
    rw [show orderOf y = orderOf x from (Subgroup.orderOf_coe x.val).trans
      (Subgroup.orderOf_coe x)]
    exact hx
  have hcenter := central_of_normal_card_two (pCore 2 I) hcards.2
  have hIc : I ≤ centralizer ({y} : Set (alternatingGroup (Fin 5))) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_center_iff.mp (hcenter x.property) ⟨a, ha⟩)
  have hpI : IsPGroup 2 I :=
    (alternatingGroup.isPGroup_centralizer_involution_of_degree_le_six
      (by decide : 5 ≤ 6) y hy).of_injective (inclusion hIc) (inclusion_injective hIc)
  obtain ⟨m, hm⟩ := hpI.exists_card_eq
  have hcop : Nat.Coprime (Nat.card I) 3 := by
    rw [hm]
    exact (by decide : Nat.Coprime 2 3).pow_left m
  norm_num [hcards.1] at hcop

/-- The original point action prevents the star quotient from being A₅. -/
theorem not_alternating_star
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ¬ Nonempty (HStar F.H ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  let q : F.H →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (starMap F)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 F.H := by
    rw [show q = _ from rfl, MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact QuotientGroup.ker_mk' _
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  let f : B →* alternatingGroup (Fin 5) := q.comp (inclusion hBH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap (inclusion hBH))
    rw [hqk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBH)
  let S : Sylow 2 (alternatingGroup (Fin 5)) :=
    (T.subtype (F.invariant 1)).mapSurjective hq
  have hS : (S : Subgroup (alternatingGroup (Fin 5))) ≤ f.range := by
    change ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map q ≤ f.range
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⟨t.val, (show (T : Subgroup G) ≤ B from le_sup_right) ht⟩, rfl⟩
  have hc : Nat.card S = 4 := by
    rw [S.card_eq_multiplicity]
    norm_num [nat_card_alternatingGroup, Nat.factorial]
    decide +kernel
  apply alternating_five_impossible f.range
  · rw [← hc]
    exact card_dvd_of_le hS
  · exact point_image_ratio h structural f hk

/-- The A₅ residual alternative determines the actual star quotient as S₅. -/
theorem exists_symmetric_star
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hAlt : AlternatingResidual F) : Nonempty (HStar F.H ≃* ChapterJ.S5) := by
  obtain ⟨e⟩ := hAlt
  have hnorm : (T : Subgroup G) ≤ normalizer (K F : Set G) :=
    (F.invariant 1).trans (le_normalizer_embedded_pResidual 2 F.H)
  have hcases := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    (K F) T hnorm T.isPGroup' e
  rw [← residual_product F] at hcases
  exact hcases.resolve_left (not_alternating_star h structural)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
