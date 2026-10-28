module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDihedralExclusion
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSecondKernelOrder
public import Theory.GroupTheory.SylowFiveKernelConjugacy
public import Theory.GroupAction.CoprimeNormalizerDecomposition

/-!
# The original quintic span has order thirty-two

Full movement of UH descends to UH/ZT.  A faithful order-twenty actor on
thirty-two elements has a normal five-subgroup; coprime splitting leaves
an invariant moving subgroup of order sixteen containing every displacement.
This contradicts full movement.  Consequently UH has order thirty-two,
and the exact central pairing radical is the original central line.
The full radius-two kernel may be larger than UH and is not bounded here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem twenty_actor_thirty_two_displacement
    {A W : Type*} [Group A] [Finite A] [Group W] [Finite W] [IsMulCommutative W]
    (α : A →* MulAut W) (hα : Function.Injective α)
    (hA : Nat.card A = 20) (hW : Nat.card W = 32) :
    ∃ B : Subgroup W, Nat.card B = 16 ∧ ∀ a : A, ∀ w : W, w⁻¹ * α a w ∈ B := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : MulDistribMulAction A W := MulDistribMulAction.compHom _ α
  let P : Sylow 5 A := Classical.choice inferInstance
  let : Subsingleton (Sylow 5 A) := Sylow.subsingleton_five_of_card_twenty hA
  let : (P : Subgroup A).Normal := P.normal_of_subsingleton
  have hP : Nat.card P = 5 := by rw [P.card_eq_multiplicity,hA]; decide +kernel
  let F := FixedPoints.subgroup P W
  let B := commutatorAction P W
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
  have hFP := fixedPoints_isInvariant_of_normalizing_actor (V := W)
    (⊤ : Subgroup A) (P : Subgroup A) (by rw [normalizer_eq_top])
  have hBP := commutatorAction_isInvariant_of_normalizing_actor (V := W)
    (⊤ : Subgroup A) (P : Subgroup A) (by rw [normalizer_eq_top])
  let : IsInvariant A W F := ⟨fun a w => hFP.invariant ⟨a,mem_top a⟩ w⟩
  let : IsInvariant A W B := ⟨fun a w => hBP.invariant ⟨a,mem_top a⟩ w⟩
  let : IsCyclic F := isCyclic_of_prime_card hF
  have hAut : Nat.card (MulAut F) = 1 := by rw [IsCyclic.card_mulAut,hF]; decide
  let : Subsingleton (MulAut F) := (Nat.card_eq_one_iff_unique.mp hAut).1
  have hfixed (a : A) (f : F) : α a (f : W) = f :=
    congrArg Subtype.val (MulEquiv.congr_fun
      (Subsingleton.elim (MulDistribMulAction.toMulAut A F a) 1) f)
  have hc : IsCompl F B :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : W => mul_comm x y))
      (by rw [hP,hW]; decide) inferInstance
  have hB : Nat.card B = 16 := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint F B
      (by rw [normalizer_eq_top]; exact le_top) hc.disjoint
    rw [hc.sup_eq_top,card_top,hF,hW] at hh
    omega
  refine ⟨B,hB,?_⟩
  intro a w
  obtain ⟨f,hf,b,hb,rfl⟩ := Subgroup.mem_sup.mp
    (show w ∈ F ⊔ B by rw [hc.sup_eq_top]; exact mem_top w)
  have hf' := hfixed a ⟨f,hf⟩
  have hb' : α a b ∈ B := (IsInvariant.invariant (A := A) (G := W) (H := B) a b).mp hb
  have he : (f*b)⁻¹ * α a (f*b) = b⁻¹ * α a b := by
    rw [map_mul,hf',mul_inv_rev]
    group
  rw [he]
  exact B.mul_mem (B.inv_mem hb) hb'

/-- The actual original span and central pairing radical have their exact
orders and markings; the larger full centralizer kernel is retained. -/
theorem source_quintic_span_card_and_core_radical
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
    Nat.card UH = 32 ∧
      UH ⊓ centralizer (H.pCoreIn 2 : Set G) = centralInvolutions T := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let Q := H.pCoreIn 2
  obtain ⟨hN,α,hker,hnot,hα⟩ :=
    source_quintic_faithful_center_layer_action hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  let W := U ⧸ Z.subgroupOf U
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let q := QuotientGroup.mk' (pCore 2 H)
  let β := QuotientGroup.lift (pCore 2 H) α hker.ge
  have hβ : Function.Injective β :=
    (QuotientGroup.injective_lift_iff _ α hker.ge).mpr hker.symm
  let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZ : Nat.card (Z.subgroupOf U) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv).trans
      (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hfull : U = ⁅U,H⁆ := by
    obtain ⟨g,hg,hDQ,hne,hVI,hTI,hprod,hcomm,hfull⟩ :=
      source_quintic_middle_core_product hG T hempty hM hu hmany hcard e H hH hi
    exact hfull
  have hU32 : Nat.card U = 32 := by
    have hc := (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).2
    change Nat.card U = 32 ∨ Nat.card U = 64 at hc
    rcases hc with he | he
    · exact he
    exfalso
    have hW : Nat.card W = 32 := by
      have hh := (Z.subgroupOf U).card_mul_index
      change Nat.card (Z.subgroupOf U) * Nat.card W = Nat.card U at hh
      rw [hZ,he] at hh
      omega
    obtain ⟨eS⟩ := (source_quintic_suzuki_zero_quotient hG T hempty hM hu hmany hcard e H hH hi).2
    have hA : Nat.card (H ⧸ pCore 2 H) = 20 :=
      (Nat.card_congr eS.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
    obtain ⟨B,hB,hdis⟩ := twenty_actor_thirty_two_displacement β hβ hA hW
    let D := (B.comap π).map U.subtype
    have hUD : U ≤ D := by
      rw [hfull]
      apply commutator_le.mpr
      intro u hu' h hh
      let uU : U := ⟨u,hu'⟩
      let hH : H := ⟨h,hh⟩
      let y : U := ⟨h*(u⁻¹)*h⁻¹,
        (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy (localModule T M) H hh) u⁻¹).mp
          (U.inv_mem hu')⟩
      have hy : π y = α hH (π uU⁻¹) := (hα hH uU⁻¹).symm
      have hd : π (uU*y) ∈ B := by
        rw [map_mul,hy]
        have hx := hdis (q hH) (π uU⁻¹)
        change (π uU⁻¹)⁻¹ * α hH (π uU⁻¹) ∈ B at hx
        simpa only [map_inv,inv_inv] using hx
      have hm := mem_map_of_mem U.subtype (show uU*y ∈ B.comap π from hd)
      change u*(h*u⁻¹*h⁻¹) ∈ D at hm
      simpa only [commutatorElement_def,mul_assoc] using hm
    have htop : B = ⊤ := by
      apply top_unique
      intro w _
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
      obtain ⟨v,hv,he⟩ := hUD u.property
      have hvu : v = u := Subtype.ext he
      exact hvu ▸ hv
    have hbcard : Nat.card B = Nat.card W := by rw [htop,card_top]
    omega
  obtain ⟨_,hN',hE,hQcard,hdual⟩ := source_quintic_second_kernel_card_sixteen
    hG T hempty hM hu hmany hcard e H hH hi
  have hEcard : Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = 2 := by
    change 16 * Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = Nat.card U at hdual
    rw [hU32] at hdual
    omega
  have hZH : Z ≤ centralizer (H : Set G) := le_centralizer_iff.mp
    (Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)).2.2.2.2.2.2
  have hZE : Z ≤ U ⊓ centralizer (Q : Set G) :=
    le_inf hZU (hZH.trans (centralizer_le (pCoreIn_le 2 H)))
  have hZEeq : Z = U ⊓ centralizer (Q : Set G) :=
    eq_of_le_of_card_ge hZE (by rw [hEcard,plane_centralInvolutions_card T M hM.1.2 hcard e])
  exact ⟨hU32,hZEeq.symm⟩

end CFSG.Quasithin.Chapter14.Section06
