module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSecondKernelDuality
public import Theory.GroupAction.FiveSmallDerived
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# The literal full second-kernel quotient has order sixteen

A faithful actor of order ten or twenty has a unique normal Sylow five.
On thirty-two elements its fixed subgroup has order two, so normality makes
the unique nonidentity fixed element global.  The actual reciprocal fixed
preimage excludes this, leaving precisely sixteen elements in QH/C.
The full denominator C is unchanged and its order is not bounded here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem small_quintic_actor_fixed_point
    {A W : Type*} [Group A] [Finite A] [Group W] [Finite W]
    (α : A →* MulAut W) (hα : Function.Injective α)
    (hA : Nat.card A = 10 ∨ Nat.card A = 20) (hW : Nat.card W = 32) :
    ∃ w : W, w ≠ 1 ∧ ∀ a : A, α a w = w := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : MulDistribMulAction A W := MulDistribMulAction.compHom _ α
  let P : Sylow 5 A := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity]
    rcases hA with h | h <;> rw [h] <;> decide +kernel
  have hi : (P : Subgroup A).index ≤ 4 := by
    have hh := (P : Subgroup A).card_mul_index
    rw [hP] at hh
    rcases hA with h | h <;> omega
  have hn : Nat.card (Sylow 5 A) = 1 := by
    have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero (P : Subgroup A).index_ne_zero_of_finite) P.card_dvd_index
    have hm := card_sylow_modEq_one 5 A
    change Nat.card (Sylow 5 A) % 5 = 1 % 5 at hm
    omega
  let : Subsingleton (Sylow 5 A) := (Nat.card_eq_one_iff_unique.mp hn).1
  let : (P : Subgroup A).Normal := P.normal_of_subsingleton
  let F := FixedPoints.subgroup P W
  have hmove : F ≠ ⊤ := by
    intro he
    have hpbot : (P : Subgroup A) = ⊥ := by
      apply bot_unique
      intro a ha
      apply mem_bot.mpr
      apply hα
      ext w
      have hw : w ∈ F := he ▸ mem_top w
      have hh := hw ⟨a,ha⟩
      change α a w = w at hh
      simpa only [map_one,MulAut.one_apply] using hh
    have hh : Nat.card P = 1 := hpbot ▸ card_bot
    omega
  have hF : Nat.card F = 2 := by
    have hb := Theory.GroupAction.sixteen_mul_fixed_card_le_of_five_action hP
      (IsPGroup.of_card (p := 2) (n := 5) hW) hmove
    have hm := P.isPGroup'.card_modEq_card_fixedPoints W
    change Nat.card W % 5 = Nat.card F % 5 at hm
    change 16 * Nat.card F ≤ Nat.card W at hb
    rw [hW] at hb hm
    have hp := Nat.card_pos (α := F)
    omega
  have hinv := fixedPoints_isInvariant_of_normalizing_actor (V := W)
    (⊤ : Subgroup A) (P : Subgroup A) (by rw [normalizer_eq_top])
  obtain ⟨w,hw,hall⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  have hw' : (w : W) ≠ 1 := fun he => hw (Subtype.ext he)
  refine ⟨w,hw',?_⟩
  intro a
  have hmem : α a (w : W) ∈ F :=
    (hinv.invariant ⟨a,mem_top a⟩ w).mp w.property
  have hne : (⟨α a (w : W),hmem⟩ : F) ≠ 1 := by
    intro he
    apply hw'
    exact (α a).injective ((congrArg Subtype.val he).trans (α a).map_one.symm)
  exact congrArg Subtype.val (hall _ hne)

omit [Finite G] in
private theorem quotient_fixed_eq_one_of_preimage
    (H Q C : Subgroup G) [(C.subgroupOf Q).Normal]
    (hHQ : H ≤ normalizer (Q : Set G))
    (hfix : commutatorPreimage Q H C = C)
    (α : H →* MulAut (Q ⧸ C.subgroupOf Q))
    (hα : ∀ h : H, ∀ q : Q,
      α h (QuotientGroup.mk' (C.subgroupOf Q) q) =
        QuotientGroup.mk' (C.subgroupOf Q)
          ⟨(h : G)*(q : G)*(h : G)⁻¹,
            (mem_normalizer_iff.mp (hHQ h.property) q).mp q.property⟩)
    (w : Q ⧸ C.subgroupOf Q) (hw : ∀ h : H, α h w = w) : w = 1 := by
  let π := QuotientGroup.mk' (C.subgroupOf Q)
  let F : Subgroup (Q ⧸ C.subgroupOf Q) := {
    carrier := {x | ∀ h : H, α h x = x}
    one_mem' := fun h => (α h).map_one
    mul_mem' := fun hx hy h => by rw [map_mul,hx h,hy h]
    inv_mem' := fun hx h => by rw [map_inv,hx h] }
  let D := (F.comap π).map Q.subtype
  have hDC : D ≤ C := by
    rw [←hfix]
    apply le_commutatorPreimage (map_subtype_le _)
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro h hh x ⟨x,hx,rfl⟩
    have he := hα ⟨h,hh⟩ x
    have hx' : ∀ a : H, α a (π x) = π x := hx
    rw [hx' ⟨h,hh⟩] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp he.symm
    change h*(x : G)*h⁻¹/(x : G) ∈ C at hc
    simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using hc
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) w
  have hq : (q : G) ∈ D := mem_map_of_mem Q.subtype hw
  exact QuotientGroup.eq_one_iff q |>.mpr (hDC hq)

/-- The actual full original core quotient has order sixteen; its fixed
preimage and the resulting exact radical cardinality retain the same kernel. -/
theorem source_quintic_second_kernel_card_sixteen
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let UH := conjugateSpanBy (localModule T M) H
    let QH := H.pCoreIn 2
    let C := H ⊓ centralizer (UH : Set G)
    commutatorPreimage QH H C = C ∧
      ∃ hN : (C.subgroupOf QH).Normal,
        letI := hN
        IsElementaryAbelian 2 (QH ⧸ C.subgroupOf QH) ∧
          Nat.card (QH ⧸ C.subgroupOf QH) = 16 ∧
          16 * Nat.card (UH ⊓ centralizer (QH : Set G) : Subgroup G) = Nat.card UH := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨hfix,hN,hE,hdual,hlo,hhi⟩ :=
    source_quintic_second_kernel_fixed_and_dual_card hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  let := hE
  let W := Q ⧸ C.subgroupOf Q
  have hnot32 : Nat.card W ≠ 32 := by
    intro hc
    obtain ⟨hCQ,hN',hE',α,hker,hnot,hbound,hα⟩ :=
      source_quintic_faithful_second_kernel_action hG T hempty hM hu hmany hcard e H hH hi
    let q := QuotientGroup.mk' (pCore 2 H)
    let β := QuotientGroup.lift (pCore 2 H) α hker.ge
    have hβ : Function.Injective β :=
      (QuotientGroup.injective_lift_iff _ α hker.ge).mpr hker.symm
    have hA : Nat.card (H ⧸ pCore 2 H) = 10 ∨ Nat.card (H ⧸ pCore 2 H) = 20 := by
      rcases Section02.SolvableAmalgam.source_index_five_models
        hG T hempty hM hu hmany hcard e H hH.1 hi with hd | hs
      · exact Or.inl ((Nat.card_congr hd.some.toEquiv).trans DihedralGroup.nat_card)
      · exact Or.inr ((Nat.card_congr hs.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card)
    obtain ⟨w,hw,hall⟩ := small_quintic_actor_fixed_point β hβ hA hc
    exact hw (quotient_fixed_eq_one_of_preimage H Q C
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
      hfix α hα w (fun h => hall (q h)))
  have hcardW : Nat.card W = 16 := by
    change 16 ≤ Nat.card W at hlo
    change Nat.card W ≤ 32 at hhi
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    have hnle : n ≤ 5 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
      simpa only [hn] using hhi)
    interval_cases n <;> norm_num at hn <;> omega
  refine ⟨hfix,hN,hE,hcardW,?_⟩
  change Nat.card W * Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = Nat.card U at hdual
  rwa [hcardW] at hdual

end CFSG.Quasithin.Chapter14.Section06
