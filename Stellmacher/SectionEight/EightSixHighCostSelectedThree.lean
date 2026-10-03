module
public import Stellmacher.SectionEight.EightSixHighCostResidualFixedFree
public import Stellmacher.SectionEight.EightSixHighCostSelectedFixedFree
public import Theory.GroupAction.RankThreeBinaryCoatomFixedCard

/-!
# The selected residual image has order three

In the original selected high-cost configuration of Stellmacher (8.6),
retain elementary D and the supplied literal action of the next stabilizer
on Vnext/Znext, with its exact next two-core kernel. The image of O²(E)
for the selected subgroup E has order three. No image size or factor
transitivity is assumed.

The selected image is nontrivial because it acts without fixed cosets,
whereas the actual order-eight actor image ensures the quotient is
nontrivial. The geometric coatom commutator relation makes the A0-image
centralize this selected image. Its index in the actual A-image divides
two. Index one would put the selected image in the trivial whole-A fixed
subgroup, so the index is two. The order-three coatom fixed-subgroup theorem
then bounds the nontrivial selected three-group image by three.

This identifies the selected cubic factor used to transport the fixed-free
action in (8.6)(c3), printed p.41, after the factor description in (21) on
p.45. The final quotient-action statement is a separate consumer.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative commutatorElement
universe u
public theorem eight_six_high_cost_selected_residual_card_three
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let W := V ⧸ Z.subgroupOf V
    ∀ (_hW : IsElementaryAbelian 2 W) (action : P →* MulAut W),
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  actor.property) point).mp point.property⟩) →
      action.ker = pCore 2 P →
      Nat.card (((twoResidualIn E).subgroupOf P).map action) = 3 := by
  classical
  let _ := hN
  dsimp only
  intro hW action hformula hkernel
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let Abar := (A.subgroupOf P).map action
  let A0bar := (A0.subgroupOf P).map action
  let F := ((twoResidualIn P).subgroupOf P).map action
  let B := twoResidualIn E
  let Bbar := (B.subgroupOf P).map action
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ P := hAE.trans geom.group_le
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hA0bar : A0bar ≤ Abar := Subgroup.map_mono (Subgroup.subgroupOf_mono P hA0A)
  have hBF : Bbar ≤ F := Subgroup.map_mono (Subgroup.subgroupOf_mono P
    (eight_six_residual_mono E P geom.group_le))
  have hAdata := eight_six_high_cost_actor_image_data ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hFdata := eight_six_high_cost_residual_irreducible_fixed_free ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hfaith := eight_six_high_cost_actor_residual_centralizer_trivial ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hFthree : IsPGroup 3 F := eight_six_next_residual_action_is_three_group
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL hN hW action hformula hkernel.ge
  have hBfree : FixedPoints.subgroup Bbar W = ⊥ :=
    eight_six_high_cost_selected_residual_fixed_free ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hN hW action hformula hkernel.ge
  have hBne : Bbar ≠ ⊥ := by
    intro hbot
    have hWone (w : W) : w = 1 := by
      have hw : w ∈ FixedPoints.subgroup Bbar W := by
        intro b
        have hb : (b : MulAut W) = 1 := hbot.le b.property
        change (b : MulAut W) w = w
        rw [hb]
        rfl
      exact hBfree.le hw
    have hAbot : Abar = ⊥ := by
      apply bot_unique
      intro a _
      apply MulEquiv.ext
      intro w
      exact (hWone (a w)).trans (hWone w).symm
    have h1 := Subgroup.card_eq_one.mpr hAbot
    have h8 : Nat.card Abar = 8 := hAdata.2.1
    omega
  have hRnative : (QAt Γ cp.firstStep).subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hA0central : A0bar ≤ Subgroup.centralizer (Bbar : Set (MulAut W)) := by
    rintro x ⟨a, ha0, rfl⟩ y ⟨b, hb, rfl⟩
    have hk : ⁅b, a⁆ ∈ action.ker := by
      rw [hkernel, ← hRnative]
      exact geom.coatom_commutator (Subgroup.commutator_mem_commutator
        (twoResidualIn_le E hb) ha0)
    have hone : ⁅action b, action a⁆ = 1 := by
      rw [← map_commutatorElement]
      exact MonoidHom.mem_ker.mp hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  let K := A0bar.subgroupOf Abar
  have hindex : A0.relIndex A = 2 := by
    have hh := (A0.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0A).toEquiv] at hh
    change A0.relIndex A * Nat.card A0 = Nat.card A at hh
    have hc : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    have hp : 0 < Nat.card A0 := Nat.card_pos
    nlinarith
  have hKdiv : K.index ∣ 2 := by
    have hdvd : A0bar.relIndex Abar ∣ (A0.subgroupOf P).relIndex (A.subgroupOf P) := by
      change ((A0.subgroupOf P).map action).relIndex ((A.subgroupOf P).map action) ∣ _
      rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq]
      exact Subgroup.relIndex_dvd_of_le_left _ le_sup_left
    rw [Subgroup.relIndex_subgroupOf hAP, hindex] at hdvd
    exact hdvd
  have hKindex : K.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hKdiv with hone | htwo
    · have hAA0 : Abar ≤ A0bar := Subgroup.relIndex_eq_one.mp hone
      have hBC : Bbar ≤ Subgroup.centralizer (Abar : Set (MulAut W)) :=
        Subgroup.le_centralizer_iff.mp (hAA0.trans hA0central)
      exact (hBne (le_bot_iff.mp (hFdata.2 ▸ le_inf hBF hBC))).elim
    · exact htwo
  let _ : ((twoResidualIn P).subgroupOf P).Normal := twoResidualIn_normal P
  have hAF : Abar ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    (Subgroup.map_mono (show A.subgroupOf P ≤
      Subgroup.normalizer ((twoResidualIn P).subgroupOf P : Set P) from
        Subgroup.le_normalizer_of_normal)).trans (Subgroup.le_normalizer_map action)
  let _ : IsElementaryAbelian 2 Abar := hAdata.1
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer Abar F hAF
  let _ : FaithfulSMul Abar F := faithfulSMul_iff.mpr (by
    intro a ha'
    have hcent : (a : MulAut W) ∈ Subgroup.centralizer (F : Set (MulAut W)) := by
      intro f hf
      have hh := congrArg Subtype.val (ha' (⟨f, hf⟩ : F))
      change (a : MulAut W) * f * (a : MulAut W)⁻¹ = f at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact Subtype.ext (show (a : MulAut W) = 1 from
      (show (a : MulAut W) ∈ (⊥ : Subgroup (MulAut W)) from hfaith ▸ ⟨a.property, hcent⟩)))
  have hfixed (a : Abar) (ha' : a ≠ 1) :
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9 := by
    let J := FixedPoints.subgroup (Subgroup.zpowers a) F
    let C := F ⊓ Subgroup.centralizer (Subgroup.zpowers (a : MulAut W) : Set (MulAut W))
    have hcent (x : J) : ((x : F) : MulAut W) ∈ C := by
      refine ⟨(x : F).property, ?_⟩
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val (x.property ⟨a, Subgroup.mem_zpowers a⟩)
      change (a : MulAut W) * ((x : F) : MulAut W) * (a : MulAut W)⁻¹ = ((x : F) : MulAut W) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    let inclusion : J → C := fun x => ⟨((x : F) : MulAut W), hcent x⟩
    have hinj : Function.Injective inclusion := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : C => (z : MulAut W)) hxy
    exact (Nat.card_le_card_of_injective inclusion hinj).trans (hAdata.2.2 a ha')
  have hBfixed : Bbar.subgroupOf F ≤ FixedPoints.subgroup K F := by
    intro b hb a
    apply Subtype.ext
    change ((a : Abar) : MulAut W) * (b : MulAut W) * ((a : Abar) : MulAut W)⁻¹ = (b : MulAut W)
    exact mul_inv_eq_iff_eq_mul.mpr (hA0central a.property _ hb).symm
  have hCne : FixedPoints.subgroup K F ≠ ⊥ := by
    intro hbot
    apply hBne
    apply bot_unique
    intro b hb
    have hh : (⟨b, hBF hb⟩ : F) ∈ FixedPoints.subgroup K F := hBfixed hb
    rw [hbot] at hh
    exact congrArg Subtype.val hh
  have hCcard := rank_three_binary_coatom_fixed_card hAdata.2.1 hFthree hfixed K hKindex hCne
  have hbound : Nat.card Bbar ≤ 3 := by
    have hh := Subgroup.card_le_of_le hBfixed
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBF).toEquiv, hCcard] at hh
    exact hh
  obtain ⟨n, hn⟩ := (hFthree.to_le hBF).exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra h
    have h9 : 9 ≤ 3 ^ n := Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (show 2 ≤ n by omega)
    rw [← hn] at h9
    omega
  interval_cases n
  · exact (hBne (Subgroup.card_eq_one.mp hn)).elim
  · exact hn

end Stellmacher.SectionEight
