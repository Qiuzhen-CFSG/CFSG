module
public import Stellmacher.SectionEight.EightSixCostFourInitialPairFixedFree
public import Stellmacher.SectionEight.EightSixInitialPairNormality
public import Stellmacher.SectionEight.EightSixInitialThreeCard
public import Stellmacher.SectionEight.EightSixCostFourCentralQuotient
public import Theory.GroupAction.CubicOrbitElementarySixteen
/-!
# The actual cost-four cubic orbit is elementary sixteen

The selected cost-four configuration produces an actual initial-residual
element t of order three. If U is the selected E-closure of the initial
center, then U together with its t-conjugate generates an elementary group
of order sixteen inside the initial pair. Both Q and the initial residual
normalize this subgroup, and t fixes only its identity.

The supplied three-Sylow acts on the literal normal initial pair by native
conjugation. Its order-three generator is fixed-free there. The central
initial center has order four, U is elementary eight, and Q modulo that
center is elementary. These facts supply every hypothesis of the generic
cubic-orbit theorem on the restricted native action. Mapping its conclusion
back gives the ambient subgroup. The same central commutator bound gives
Q-normalization; the residual supplement by the actual three-Sylow gives
normalization by the initial residual.

Source: Stellmacher (8.6)(b3), printed p.44, the elementary-sixteen construction.
The following commutator identification recovers W=[U,Ea]; this theorem
retains the concrete orbit and element needed to verify that identification.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative commutatorElement
universe u
public theorem eight_six_cost_four_cubic_orbit
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
    ∃ t : G, t ∈ EAt ctx.Γ ctx.criticalPath.a ∧ orderOf t = 3 ∧
      let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
      let W := U ⊔ U.conjBy t
      IsElementaryAbelianSubgroup 2 W ∧ Nat.card W = 16 ∧
        W ≤ (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
          (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ∧
        Q ≤ Subgroup.normalizer (W : Set G) ∧
        EAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (W : Set G) ∧
        W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let F := EAt Γ cp.a
  let Z := ZAt Γ cp.a
  let U := conjugateClosure Z E
  let R := (VAt Γ previous ⊓ QAt Γ cp.a) ⊔ (VAt Γ cp.firstStep ⊓ QAt Γ cp.a)
  have hRQ : R ≤ Q := data.core_generation ▸ le_sup_left
  have hQL : Q ≤ L := hQ ▸ twoCoreIn_le L
  have hQP : Q ≤ P := hQL.trans data.closure_le
  have hRnormal := eight_six_initial_pair_normal ctx hquot hlength previous hprev
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRnormal.1).mp hRnormal.2
  let sylow : Sylow 3 P := default
  let T : Subgroup G := (sylow : Subgroup P).map P.subtype
  have hT : IsSylowIn 3 T P := ⟨sylow,rfl⟩
  have hTP : T ≤ P := Subgroup.map_subtype_le _
  have hTthree : IsPGroup 3 T := sylow.isPGroup'.map P.subtype
  have hTF : T ≤ F := by
    change T ≤ Γ.twoResidualAt cp.a
    rw [Γ.twoResidualAt_def]
    exact eight_six_three_subgroup_le_residual T P hTP hTthree
  have hTcard : Nat.card T = 3 := eight_six_initial_three_card ctx hquot T hT
  let _ : IsCyclic T := isCyclic_of_prime_card hTcard
  obtain ⟨t,htgen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic T)
  have htorder : orderOf (t:G) = 3 := by
    rw [←T.subtype_apply,orderOf_injective T.subtype T.subtype_injective,
      orderOf_eq_card_of_zpowers_eq_top htgen,hTcard]
  have ht3 : (t:G)^3=1 := htorder ▸ pow_orderOf_eq_one (t:G)
  have hgen : Subgroup.zpowers (t:G) = T := by
    have hh := congrArg (Subgroup.map T.subtype) htgen
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,Subgroup.range_subtype,Subgroup.subtype_apply] using hh
  have hfixedR : R ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
    eight_six_cost_four_initial_pair_fixed_free ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost T hT
  have hfixedOne : R ⊓ Subgroup.centralizer ({(t:G)} : Set G) = ⊥ := by
    apply bot_unique
    intro r hr
    have hTR : T ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [←hgen]
      apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hr.2).symm
    have hrt : r ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (hTR hs)
    have hh : r ∈ R ⊓ Subgroup.centralizer (T : Set G) := ⟨hr.1,hrt⟩
    simpa only [hfixedR,Subgroup.mem_bot] using hh
  let tN : Subgroup.normalizer (R : Set G) := ⟨t,hPR (hTP t.property)⟩
  let a : MulAut R := R.normalizerMonoidHom tN
  have haformula (r:R) : (a r:G) = (t:G)*r*(t:G)⁻¹ := rfl
  have hacube : a^3=1 := by
    have hh : tN^3=1 := Subtype.ext ht3
    change (R.normalizerMonoidHom tN)^3=1
    rw [←map_pow,hh,map_one]
  have hafixed : ∀ r:R, a r=r → r=1 := by
    intro r hr
    apply Subtype.ext
    have hh := congrArg Subtype.val hr
    change (t:G)*(r:G)*(t:G)⁻¹=(r:G) at hh
    have hrt : (r:G) ∈ Subgroup.centralizer ({(t:G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hx : (r:G) ∈ R ⊓ Subgroup.centralizer ({(t:G)} : Set G) := ⟨r.property,hrt⟩
    change (r:G)=1
    simpa only [hfixedOne,Subgroup.mem_bot] using hx
  have hZU : Z ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hUV : U ≤ VAt Γ cp.firstStep := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    (geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hUR : U ≤ R := (le_inf hUV hcore).trans le_sup_right
  have hZR : Z ≤ R := hZU.trans hUR
  have hUcard : Nat.card U = 8 := eight_six_selected_orbit_card_eight
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hUelem : IsElementaryAbelian 2 U := eight_six_selected_orbit_elementary ctx E hcore
  let _ := hUelem
  have hZC : Z ≤ Subgroup.centralizer (Q : Set G) :=
    (eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data).2.2.2
  have hZcenter : Z.subgroupOf R ≤ Subgroup.center R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hZC hz) (r:G) (hRQ r.property)
  have hZt : Z.conjBy (t:G) = Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (stabilizer_le_normalizer_z Γ cp.a (hTP t.property))
  have hRmap : R.conjBy (t:G) = R := Subgroup.mem_normalizer_iff_map_conj_eq.mp tN.property
  have hUtR : U.conjBy (t:G) ≤ R := hRmap ▸ Subgroup.map_mono hUR
  have hmap (H : Subgroup G) (hHR : H ≤ R) :
      ((H.subgroupOf R).map a.toMonoidHom).map R.subtype = H.conjBy (t:G) := by
    rw [Subgroup.map_map]
    have hh : R.subtype.comp a.toMonoidHom = (MulAut.conj (t:G)).toMonoidHom.comp R.subtype := by
      ext r
      rfl
    rw [hh,←Subgroup.map_map,Subgroup.map_subgroupOf_eq_of_le hHR]
    rfl
  have hZia : (Z.subgroupOf R).map a.toMonoidHom = Z.subgroupOf R := by
    apply Subgroup.map_injective R.subtype_injective
    rw [hmap Z hZR,hZt,Subgroup.map_subgroupOf_eq_of_le hZR]
  obtain ⟨quot,hquotElem⟩ := eight_six_cost_four_central_quotient ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  let _ := quot.groupX
  let _ := quot.finiteX
  let _ : IsElementaryAbelian 2 quot.X := hquotElem
  have hcommQ : ⁅Q,Q⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hh : ⁅(⟨x,hx⟩:Q),⟨y,hy⟩⁆ ∈ quot.projection.ker := by
      rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [quot.kernel_eq] at hh
    exact hh
  have hcomi : ⁅U.subgroupOf R,(U.subgroupOf R).map a.toMonoidHom⁆ ≤ Z.subgroupOf R := by
    apply (Subgroup.map_le_map_iff_of_injective R.subtype_injective).mp
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hUR,hmap U hUR,
      Subgroup.map_subgroupOf_eq_of_le hZR]
    exact (Subgroup.commutator_mono (hUR.trans hRQ) (hUtR.trans hRQ)).trans hcommQ
  have hUiElem : IsElementaryAbelian 2 (U.subgroupOf R) := IsElementaryAbelian.subgroupOf hUR
  have hZiCard : Nat.card (Z.subgroupOf R) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv).trans hcard
  have hUiCard : Nat.card (U.subgroupOf R) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv).trans hUcard
  obtain ⟨hWiElem,hWiCard,hWia⟩ := MulAut.elementary_sixteen_of_cubic_orbit_eight
    (Z.subgroupOf R) (U.subgroupOf R) (Subgroup.subgroupOf_mono R hZU) hZcenter
    hZiCard hUiCard hUiElem a hacube hafixed hZia hcomi
  let Wi := U.subgroupOf R ⊔ (U.subgroupOf R).map a.toMonoidHom
  let W := U ⊔ U.conjBy (t:G)
  have hWmap : Wi.map R.subtype = W := by
    rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hUR,hmap U hUR]
  have hWR : W ≤ R := sup_le hUR hUtR
  have hZW : Z ≤ W := hZU.trans le_sup_left
  have hWElem : IsElementaryAbelian 2 W := by
    rw [←hWmap]
    let _ := hWiElem
    exact IsElementaryAbelian.map R.subtype
  have hWcard : Nat.card W = 16 := by
    rw [←hWmap,Subgroup.card_map_of_injective R.subtype_injective]
    exact hWiCard
  have hWa : W.conjBy (t:G) = W := by
    have hh := congrArg (Subgroup.map R.subtype) hWia
    rw [Subgroup.map_map] at hh
    have hf : R.subtype.comp a.toMonoidHom = (MulAut.conj (t:G)).toMonoidHom.comp R.subtype := by
      ext r
      rfl
    rw [hf,←Subgroup.map_map,hWmap] at hh
    exact hh
  have hQN : Q ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono (hWR.trans hRQ) le_rfl).trans (hcommQ.trans hZW))
  have hTN : T ≤ Subgroup.normalizer (W : Set G) := by
    rw [←hgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hWa)
  have hFN : F ≤ Subgroup.normalizer (W : Set G) :=
    (eight_six_initial_residual_le_core_sup_three ctx hquot previous D L Q T hL hQ hT data).trans
      (sup_le hQN hTN)
  refine ⟨t,hTF t.property,htorder,hWElem,hWcard,hWR,hQN,hFN,?_⟩
  exact le_antisymm ((inf_le_inf_right _ hWR).trans hfixedOne.le) bot_le
end Stellmacher.SectionEight
