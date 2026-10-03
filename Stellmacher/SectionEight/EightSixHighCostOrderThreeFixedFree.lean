module
public import Stellmacher.SectionEight.EightSixHighCostModuleData
public import Stellmacher.SectionEight.EightSixHighCostResidualFixedFree
public import Stellmacher.SectionEight.EightSixHighCostSelectedFixedFree
public import Stellmacher.SectionEight.EightSixHighCostSelectedThree
public import Theory.GroupAction.RankThreeBinaryCubicLineOrbit

/-!
Every invariant cubic quotient subgroup in the high-cost case of Stellmacher
(8.6)(c3) acts without nontrivial fixed cosets on the next central quotient.
The hypotheses are the original selected high-cost configuration with elementary
`D`. The native module construction derives residual elementarity and supplies
the action with its exact kernel.

The selected residual image has order three and acts without fixed cosets.
Conjugation by the actual Sylow image is irreducible on the elementary residual
image. The rank-three binary cubic-line orbit theorem therefore transports this
property to every invariant subgroup of order three. For an arbitrary subgroup
representing a cubic quotient, the exact action kernel gives its image order three, and equality of the
actor image with the selected core image gives invariance. The literal action
formula finally identifies fixed quotient vectors with the commutator-in-center
condition in `QuotientQInvariantOrderThreeFixedPointFree`.

Source: Stellmacher, proof of (8.6), statements (18) and (21), p.45, concluding
(8.6)(c3), p.41. The quotient-action reading of c3 was explicitly approved by the
user after the source and finite-model audit recorded in the contract task.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise IsMulCommutative
universe u
private theorem conjugation_action_data
    {X : Type*} [Group X] [Finite X]
    (A F T : Subgroup X)
    (hAF : A ≤ Subgroup.normalizer (F : Set X))
    (hTA : T ≤ Subgroup.normalizer (A : Set X))
    (hTF : T ≤ Subgroup.normalizer (F : Set X))
    (hfaith : A ⊓ Subgroup.centralizer (F : Set X) = ⊥)
    (hfull : F ⊓ Subgroup.centralizer (A : Set X) = ⊥)
    (hfixed : ∀ a : A, a ≠ 1 → Nat.card
      (F ⊓ Subgroup.centralizer (Subgroup.zpowers (a:X) : Set X) : Subgroup X) ≤ 9)
    (hirred : IsIrreducibleSection T ⊥ F) :
    let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer A F hAF
    let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T A hTA
    let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T F hTF
    FaithfulSMul A F ∧
    FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥ ∧
    (∀ a : A, a ≠ 1 → Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9) ∧
    (∀ H : Subgroup F, IsInvariant T F H → H = ⊥ ∨ H = ⊤) ∧
    (∀ t : T, ∀ a : A, ∀ x : F, t • (a • x) = (t • a) • (t • x)) := by
  classical
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer A F hAF
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T A hTA
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T F hTF
  have hfaithful : FaithfulSMul A F := faithfulSMul_iff.mpr (by
    intro a ha
    have hcent : (a:X) ∈ Subgroup.centralizer (F : Set X) := by
      intro f hf
      have hh := congrArg Subtype.val (ha (⟨f,hf⟩:F))
      change (a:X)*f*(a:X)⁻¹=f at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact Subtype.ext (show (a:X)=1 from
      (show (a:X) ∈ (⊥ : Subgroup X) from hfaith ▸ ⟨a.property,hcent⟩)))
  refine ⟨hfaithful,?_,?_,?_,?_⟩
  · apply bot_unique
    intro f hf
    have hcent : (f:X) ∈ Subgroup.centralizer (A : Set X) := by
      intro a ha
      have hh := congrArg Subtype.val (hf (⟨⟨a,ha⟩,Subgroup.mem_top _⟩ : (⊤ : Subgroup A)))
      change a*(f:X)*a⁻¹=(f:X) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    exact Subtype.ext (show (f:X)=1 from
      (show (f:X) ∈ (⊥ : Subgroup X) from hfull ▸ ⟨f.property,hcent⟩))
  · intro a ha
    let J := FixedPoints.subgroup (Subgroup.zpowers a) F
    let C := F ⊓ Subgroup.centralizer (Subgroup.zpowers (a:X) : Set X)
    have hcent (x : J) : ((x:F):X) ∈ C := by
      refine ⟨(x:F).property,?_⟩
      rw [Subgroup.zpowers_eq_closure,Subgroup.centralizer_closure]
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val (x.property ⟨a,Subgroup.mem_zpowers a⟩)
      change (a:X)*((x:F):X)*(a:X)⁻¹=((x:F):X) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    let inclusion : J → C := fun x => ⟨((x:F):X),hcent x⟩
    have hinj : Function.Injective inclusion := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : C => (z:X)) hxy
    exact (Nat.card_le_card_of_injective inclusion hinj).trans (hfixed a ha)
  · intro H hH
    let _ := hH
    have hinv : IsConjugateInvariantBy (H.map F.subtype) T := by
      intro t x hx
      obtain ⟨f,hf,rfl⟩ := hx
      exact ⟨t • f,(IsInvariant.invariant t f).mp hf,rfl⟩
    rcases hirred.2.2 (H.map F.subtype) bot_le (Subgroup.map_subtype_le H) hinv with hb | ht
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective H F.subtype_injective).mp hb
    · right
      apply Subgroup.map_injective F.subtype_injective
      rw [ht,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  · intro t a x
    apply Subtype.ext
    change (t:X)*((a:X)*(x:X)*(a:X)⁻¹)*(t:X)⁻¹ =
      ((t:X)*(a:X)*(t:X)⁻¹)*((t:X)*(x:X)*(t:X)⁻¹)*((t:X)*(a:X)*(t:X)⁻¹)⁻¹
    group

public theorem eight_six_high_cost_order_three_fixed_point_free
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
 :
    QuotientQInvariantOrderThreeFixedPointFree
      (EAt ctx.Γ ctx.criticalPath.firstStep)
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) Q
      (ZAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  classical
  obtain ⟨hN,hW,action,hformula,hkernel,hF⟩ := eight_six_high_cost_residual_module_data
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  let _ := hN
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let Abar := ((VAt Γ previous ⊓ QAt Γ cp.a).subgroupOf P).map action
  let F := ((twoResidualIn P).subgroupOf P).map action
  let T := (S.subgroupOf P).map action
  have hAdata := eight_six_high_cost_actor_image_data ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hFdata := eight_six_high_cost_residual_irreducible_fixed_free ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hfaith := eight_six_high_cost_actor_residual_centralizer_trivial ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hTA : T ≤ Subgroup.normalizer (Abar : Set (MulAut W)) :=
    (eight_six_actor_image_eq_core_and_normalized ctx hlength previous D L Q hD hL hQ
      data action hkernel.ge).2.1
  let _ : ((twoResidualIn P).subgroupOf P).Normal := twoResidualIn_normal P
  have hAF : Abar ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    (Subgroup.map_mono (show (VAt Γ previous ⊓ QAt Γ cp.a).subgroupOf P ≤
      Subgroup.normalizer ((twoResidualIn P).subgroupOf P : Set P) from
        Subgroup.le_normalizer_of_normal)).trans (Subgroup.le_normalizer_map action)
  have hTF : T ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    (Subgroup.map_mono (show S.subgroupOf P ≤
      Subgroup.normalizer ((twoResidualIn P).subgroupOf P : Set P) from
        Subgroup.le_normalizer_of_normal)).trans (Subgroup.le_normalizer_map action)
  let _ : IsElementaryAbelian 2 Abar := hAdata.1
  let _ : IsElementaryAbelian 3 F := hF
  let _ : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).mpr hFdata.1.2.1.symm
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer Abar F hAF
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T Abar hTA
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer T F hTF
  have hconj := conjugation_action_data Abar F T hAF hTA hTF hfaith hFdata.2
    hAdata.2.2 hFdata.1
  let _ : FaithfulSMul Abar F := hconj.1
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := twoResidualIn E
  let Bbar := (B.subgroupOf P).map action
  let HB := Bbar.subgroupOf F
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hBF : Bbar ≤ F := Subgroup.map_mono (Subgroup.subgroupOf_mono P
    (eight_six_residual_mono E P geom.group_le))
  have hBcard : Nat.card Bbar = 3 := eight_six_high_cost_selected_residual_card_three
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary hN hW action hformula hkernel
  have hHBcard : Nat.card HB = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBF).toEquiv]
    exact hBcard
  have hBfree : FixedPoints.subgroup Bbar W = ⊥ :=
    eight_six_high_cost_selected_residual_fixed_free ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hN hW action hformula hkernel.ge
  have hnormalize_map (N K : Subgroup G) (hNK : N ≤ Subgroup.normalizer (K : Set G)) :
      (N.subgroupOf P).map action ≤
        Subgroup.normalizer ((K.subgroupOf P).map action : Set (MulAut W)) := by
    apply le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map action)
    intro n hn
    apply Subgroup.mem_normalizer_iff.mpr
    intro k
    change (k : G) ∈ K ↔ (n : G) * (k : G) * (n : G)⁻¹ ∈ K
    exact Subgroup.mem_normalizer_iff.mp (hNK hn) k
  have hInvOfNorm (U : Subgroup (MulAut W))
      (hAU : Abar ≤ Subgroup.normalizer (U : Set (MulAut W))) :
      IsInvariant Abar F (U.subgroupOf F) := by
    constructor
    intro a f
    change (f : MulAut W) ∈ U ↔ (a : MulAut W) * (f : MulAut W) * (a : MulAut W)⁻¹ ∈ U
    exact Subgroup.mem_normalizer_iff.mp (hAU a.property) f
  have hEB : E ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le E)).mp (twoResidualIn_normal E)
  have hBinv : IsInvariant Abar F HB := hInvOfNorm Bbar
    (hnormalize_map A B (hAE.trans hEB))
  have hAeq : Abar = (Q.subgroupOf P).map action :=
    (eight_six_actor_image_eq_core_and_normalized ctx hlength previous D L Q hD hL hQ
      data action hkernel.ge).1
  let Enext := EAt Γ cp.firstStep
  let O := twoCoreIn Enext
  have hEnext : Enext = twoResidualIn P := Γ.twoResidualAt_def _
  have hEP : Enext ≤ P := hEnext ▸ twoResidualIn_le P
  have hOcore : O = Enext ⊓ QAt Γ cp.firstStep := by
    change twoCoreIn Enext = Enext ⊓ QAt Γ cp.firstStep
    rw [hEnext, residual_core_eq_inter_core]
    rw [show QAt Γ cp.firstStep = twoCoreIn P from Γ.twoCoreAt_def _]
  have hRnative : (QAt Γ cp.firstStep).subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hRV : QAt Γ cp.firstStep = V := eight_six_high_cost_next_core_eq_v
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL hhigh hselected.1 helementary
  intro R hRE hOR hRcard hRinv v hv hfix
  have hRP : R ≤ P := hRE.trans hEP
  let Ri := R.subgroupOf P
  let U := Ri.map action
  let HU := U.subgroupOf F
  have hUF : U ≤ F := Subgroup.map_mono (Subgroup.subgroupOf_mono P (hEnext ▸ hRE))
  have hkerR : Ri ⊓ action.ker = O.subgroupOf P := by
    rw [hkernel, ← hRnative]
    ext r
    change ((r : G) ∈ R ∧ (r : G) ∈ QAt Γ cp.firstStep) ↔ (r : G) ∈ O
    constructor
    · intro h
      exact hOcore ▸ ⟨hRE h.1, h.2⟩
    · intro h
      exact ⟨hOR h, (hOcore ▸ h).2⟩
  have hindex : O.relIndex R = 3 := by
    have hh := (O.subgroupOf R).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOR).toEquiv] at hh
    change O.relIndex R * Nat.card O = Nat.card R at hh
    change Nat.card R = 3 * Nat.card O at hRcard
    have hp : 0 < Nat.card O := Nat.card_pos
    nlinarith
  have hUcard : Nat.card U = 3 := by
    change Nat.card (Ri.map action) = 3
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_left Ri action.ker, hkerR,
      Subgroup.relIndex_subgroupOf hRP]
    exact hindex
  have hHUcard : Nat.card HU = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUF).toEquiv]
    exact hUcard
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) := by
    intro q hq
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hRinv ⟨q, hq⟩)
  have hUnorm : Abar ≤ Subgroup.normalizer (U : Set (MulAut W)) := by
    rw [hAeq]
    exact hnormalize_map Q R hQR
  have hUinv : IsInvariant Abar F HU := hInvOfNorm U hUnorm
  obtain ⟨t, ht⟩ := rank_three_binary_invariant_cubic_subgroups_same_orbit
    hAdata.2.1 hconj.2.2.2.2 hconj.2.2.1 hconj.2.1 hconj.2.2.2.1
    HB HU hBinv hUinv hHBcard hHUcard
  have hUfree : FixedPoints.subgroup U W = ⊥ := by
    apply bot_unique
    intro w hw
    change w = 1
    have hpre : (t : MulAut W).symm w ∈ FixedPoints.subgroup Bbar W := by
      intro b
      have hbF : (⟨b, hBF b.property⟩ : F) ∈ HB := b.property
      have hs : t • (⟨b, hBF b.property⟩ : F) ∈ HU := by
        rw [← ht]
        exact Subgroup.smul_mem_pointwise_smul _ t HB hbF
      change (t : MulAut W) * (b : MulAut W) * (t : MulAut W)⁻¹ ∈ U at hs
      have hact := hw ⟨_, hs⟩
      change (t : MulAut W) ((b : MulAut W) ((t : MulAut W).symm w)) = w at hact
      change (b : MulAut W) ((t : MulAut W).symm w) = (t : MulAut W).symm w
      apply (t : MulAut W).injective
      exact hact.trans ((t : MulAut W).apply_symm_apply w).symm
    have h1 : (t : MulAut W).symm w = 1 := hBfree.le hpre
    have hh := congrArg (t : MulAut W) h1
    simpa only [MulEquiv.apply_symm_apply, map_one] using hh
  let vv : V := ⟨v, hRV.le hv⟩
  have hvbar : QuotientGroup.mk' (Z.subgroupOf V) vv ∈ FixedPoints.subgroup U W := by
    intro r
    obtain ⟨lift, hlift, heq⟩ := r.property
    change (r : MulAut W) (QuotientGroup.mk' (Z.subgroupOf V) vv) =
      QuotientGroup.mk' (Z.subgroupOf V) vv
    rw [← heq, hformula]
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    apply (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) _).mpr
    exact hfix lift hlift
  have hvone : QuotientGroup.mk' (Z.subgroupOf V) vv = 1 := hUfree.le hvbar
  exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) vv).mp hvone

end Stellmacher.SectionEight
