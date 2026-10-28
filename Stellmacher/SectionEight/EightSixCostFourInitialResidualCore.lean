module
public import Stellmacher.SectionEight.EightSixCostFourInitialPairFixedFree
public import Stellmacher.SectionEight.EightSixInitialPairNormality
public import Stellmacher.SectionFiveToSeven.ResidualTwoExtension
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The cost-four initial pair is the initial residual two-core

In the selected cost-four configuration of Stellmacher (8.6), the join of the
two neighboring module/core intersections is precisely O₂(Ea). The original
local context, geometric data and selected actor hypotheses are retained. The
three-Sylow subgroup used in the proof is chosen from the actual initial
stabilizer; neither this residual-core identity nor a model action is assumed.

The pair is a normal two-subgroup of the initial stabilizer and has no fixed
points under its three-Sylow T. Coprime centralizer decomposition therefore
identifies the pair with its commutator with T, placing it in Ea and then in
O₂(Ea). The proved fixed-core splitting gives Q = pair · C_Q(T). The latter
centralizer normalizes pair · T, and residual perfection eliminates this
two-group supplement to give Ea ≤ pair · T. Finally O₂(Ea) lies in the initial
two-core, which is disjoint from T, yielding the reverse containment.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b1),
printed p.44, the identity AAtilde = O₂(Ea).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement Pointwise
universe u
public theorem eight_six_cost_four_initial_pair_eq_residual_core
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)) =
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Qa := QAt Γ cp.a
  let F := EAt Γ cp.a
  let Z := ZAt Γ cp.a
  let pair := (VAt Γ previous ⊓ Qa) ⊔ (VAt Γ cp.firstStep ⊓ Qa)
  let sylow : Sylow 3 P := Classical.choice inferInstance
  let T : Subgroup G := (sylow : Subgroup P).map P.subtype
  have hT : IsSylowIn 3 T P := ⟨sylow,rfl⟩
  have hTP : T ≤ P := Subgroup.map_subtype_le _
  have hTthree : IsPGroup 3 T := sylow.isPGroup'.map P.subtype
  have hFdef : F = twoResidualIn P := Γ.twoResidualAt_def _
  have hFP : F ≤ P := hFdef ▸ twoResidualIn_le P
  have hFn : (F.subgroupOf P).Normal := by
    rw [hFdef]
    exact twoResidualIn_normal P
  have hPNF : P ≤ Subgroup.normalizer (F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFP).mp hFn
  have hTF : T ≤ F := hFdef ▸ eight_six_three_subgroup_le_residual T P hTP hTthree
  have hpairQa : pair ≤ Qa := sup_le inf_le_right inf_le_right
  have hpairNormal : NormalIn pair P := eight_six_initial_pair_normal
    ctx hquot hlength previous hprev
  have hPNpair : P ≤ Subgroup.normalizer (pair : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hpairNormal.1).mp hpairNormal.2
  have hQaTwo : IsPGroup 2 Qa := by
    change IsPGroup 2 (Γ.twoCoreAt _)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hpairTwo : IsPGroup 2 pair := hQaTwo.to_le hpairQa
  have hpairFixed : pair ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
    eight_six_cost_four_initial_pair_fixed_free ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost T hT
  let _ : Group.IsSolvable P := (edge_local_data ctx.sectionSeven Γ cp).1.2
  have hpairSolv : Group.IsSolvable pair :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hpairNormal.1)
  have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide) T pair hTthree hpairTwo
  have hpairComm : pair = ⁅pair,T⁆ := by
    have hh := Subgroup.eq_commutator_sup_centralizer_of_solvable_coprime pair T
      (hTP.trans hPNpair) hpairSolv hcop
    rwa [hpairFixed,sup_bot_eq] at hh
  have hpairF : pair ≤ F := by
    rw [hpairComm]
    exact (Subgroup.commutator_mono le_rfl hTF).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (hpairNormal.1.trans hPNF))
  have hpairCore : pair ≤ twoCoreIn F := eight_six_normal_two_subgroup_le_core pair F
    ⟨hpairF,Subgroup.normal_subgroupOf_of_le_normalizer (hFP.trans hPNpair)⟩ hpairTwo
  have hbase := eight_six_common_structure_local ctx hcenter hquot hlength hcard previous hprev
    D L Q hD hL hQ
  have hsplit := eight_six_fixed_core_splitting ctx hcenter hquot hcard previous hprev.1
    D L Q hD hL hQ data hbase.2.2.2 T hT
  let C := Q ⊓ Subgroup.centralizer (T : Set G)
  have hQtwo : IsPGroup 2 Q := hQ ▸ eight_six_two_core_is_two_group L
  have hCtwo : IsPGroup 2 C := hQtwo.to_le inf_le_left
  have hQP : Q ≤ P := (hQ ▸ twoCoreIn_le L).trans data.closure_le
  have hpairD : pair ⊓ D = Z := (eight_six_cost_four_core_quotient_card
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hcost).2
  have hZpair : Z ≤ pair := hpairD.ge.trans inf_le_left
  have hQpairC : Q = pair ⊔ C := by
    calc
      Q = pair ⊔ D := data.core_generation
      _ = pair ⊔ (C ⊔ Z) := congrArg (pair ⊔ ·) hsplit.1
      _ = pair ⊔ C := by
        rw [← sup_assoc,sup_eq_left.mpr (hZpair.trans le_sup_left)]
  let K := pair ⊔ T
  have hCK : C ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf ((inf_le_left.trans hQP).trans hPNpair)
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer (T : Set G)))).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup pair T)
  have hKnormal : (K.subgroupOf (K ⊔ C)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hCK)
  have hcover : F ≤ K ⊔ C := by
    have hh := eight_six_initial_residual_le_core_sup_three ctx hquot previous D L Q T hL hQ hT data
    change F ≤ Q ⊔ T at hh
    rw [hQpairC] at hh
    exact hh.trans_eq (sup_right_comm pair C T)
  have hFperfect : twoResidualIn F = F := by
    rw [hFdef]
    simpa only [sup_bot_eq] using twoResidualIn_sup_twoGroup_eq P (⊥ : Subgroup G)
      (IsPGroup.of_bot (p := 2)) bot_le
  have hFK : F ≤ K := by
    have hh := SectionThree.twoResidualAmbient_le_left_of_le_sup K C F hKnormal hCtwo hcover
    change twoResidualIn F ≤ K at hh
    rwa [hFperfect] at hh
  have hcoreTwo : IsPGroup 2 (twoCoreIn F) := eight_six_two_core_is_two_group F
  have hcoreNormal : NormalIn (twoCoreIn F) P :=
    ⟨(twoCoreIn_le F).trans hFP,twoCoreIn_normal_of_normal F P hFP hFn⟩
  have hcoreQa : twoCoreIn F ≤ Qa := by
    change twoCoreIn F ≤ Γ.twoCoreAt cp.a
    rw [Γ.twoCoreAt_def]
    exact eight_six_normal_two_subgroup_le_core (twoCoreIn F) P hcoreNormal hcoreTwo
  have hdisjoint : Disjoint T Qa := hTthree.disjoint_of_coprime hQaTwo (by decide)
  apply le_antisymm hpairCore
  intro x hx
  have hxK : x ∈ K := hFK (twoCoreIn_le F hx)
  have hxProduct : x ∈ (pair : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left pair T (hTP.trans hPNpair)]
    exact hxK
  obtain ⟨r,hr,t,ht,hrt⟩ := hxProduct
  have htQa : t ∈ Qa := by
    have heq : t = r⁻¹*x := by rw [← hrt]; simp
    rw [heq]
    exact Qa.mul_mem (Qa.inv_mem (hpairQa hr)) (hcoreQa hx)
  have ht1 : t = 1 := Subgroup.disjoint_def.mp hdisjoint ht htQa
  have hrx : r = x := by simpa only [ht1,mul_one] using hrt
  exact hrx ▸ hr
end Stellmacher.SectionEight
