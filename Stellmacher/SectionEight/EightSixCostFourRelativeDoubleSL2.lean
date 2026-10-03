module
public import Stellmacher.SectionOne.RelativeExceptionalAction
public import Stellmacher.SectionEight.EightSixCostFourActionProfile
public import Stellmacher.SectionEight.EightSixCostFourFullFixedIndex

/-!
# The relative double-SL2 group in the cost-four branch

On the literal quotient W=Vnext/Znext, let X be the full next-stabilizer
action image and B the actual predecessor actor image. In the selected
cost-four configuration, F=[O₂′(X),B] satisfies F B ≃ SL₂(2)×SL₂(2), and
its commutator module [W,F] has order sixteen. The original quotient
normality proof, action, and Sylow-fixed-generation data are retained.

Sylow-fixed generation makes X have trivial two-core, and its literal
automorphism action is faithful. The cost-four action profile gives B
order four and exponent two, with fixed index four for each nonidentity
element. Its full fixed index eight gives m(B)=2. Every nontrivial proper
subgroup of B has order two and the same measure, so B has minimum measure.
Source (5) excludes quadraticity of the full B-action. The proved relative
exceptional-action theorem now applies bounded (1.6) to the correct group
[O₂′(X),B]B, with the required core-free and Sylow data supplied by its
relative-group construction.

The selected geometric E has a central order-two image and cannot itself
be the Section One acting group; this theorem uses the full faithful range
and its odd-core commutator instead. Source: Stellmacher, Journal of Algebra
190 (1997), proof of (8.6), printed p.44, the bounded-(1.6) step. Whole
next-quotient wreath recognition is the subsequent argument.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
private theorem m_eq_two_of_fixed_index
    {K W : Type u} [Group K] [Group W] [Finite K] [Finite W]
    [MulDistribMulAction K W] (A : Subgroup K)
    (hindex : (FixedPoints.subgroup A W).index = 2 * Nat.card A) :
    SectionOne.m (V := W) A = 2 := by
  have hcount := (FixedPoints.subgroup A W).card_mul_index
  rw [hindex] at hcount
  have hnat : Nat.card W = 2 * (Nat.card (FixedPoints.subgroup A W) * Nat.card A) := by
    nlinarith only [hcount]
  unfold SectionOne.m
  apply (div_eq_iff (mul_ne_zero
    (by exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup A W)).ne')
    (by exact_mod_cast (Nat.card_pos (α := A)).ne'))).mpr
  exact_mod_cast hnat

private theorem four_actor_minimum
    {K W : Type u} [Group K] [Group W] [Finite K] [Finite W]
    [MulDistribMulAction K W] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (hfull : (FixedPoints.subgroup A W).index = 8)
    (hproper : ∀ t ∈ A, t ≠ 1 →
      (FixedPoints.subgroup (Subgroup.zpowers t) W).index = 4) :
    SectionOne.m (V := W) A = 2 ∧
      ∀ Y : Subgroup K, Y ≤ A → Y ≠ ⊥ →
        SectionOne.m (V := W) A ≤ SectionOne.m (V := W) Y := by
  have hm : SectionOne.m (V := W) A = 2 :=
    m_eq_two_of_fixed_index A (by rw [hA,hfull])
  refine ⟨hm,?_⟩
  intro Y hYA hYne
  have hle := Subgroup.card_le_of_le hYA
  have hdvd := Subgroup.card_dvd_of_le hYA
  rw [hA] at hle hdvd
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have hnotone : Nat.card Y ≠ 1 := fun hh => hYne (Subgroup.card_eq_one.mp hh)
  have hcases : Nat.card Y = 2 ∨ Nat.card Y = 4 := by
    interval_cases hn : Nat.card Y <;> omega
  rcases hcases with htwo | hfour
  · obtain ⟨t,ht,_⟩ := (Nat.card_eq_two_iff' (1:Y)).mp htwo
    have htG : (t:K) ≠ 1 := fun hh => ht (Subtype.ext hh)
    have ht2 : (t:K)^2=1 := elemPow_eq_one_of_isElementaryAbelian (t:K) (hYA t.property)
    have hz : Nat.card (Subgroup.zpowers (t:K)) = 2 := by
      rw [Nat.card_zpowers,orderOf_eq_prime ht2 htG]
    have hYeq : Subgroup.zpowers (t:K) = Y :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr t.property) (by rw [hz,htwo])
    have hindex := hproper t (hYA t.property) htG
    rw [hYeq] at hindex
    have hmY := m_eq_two_of_fixed_index Y (by rw [htwo,hindex])
    rw [hm,hmY]
  · have heq : Y = A := Subgroup.eq_of_le_of_card_ge hYA (by rw [hA,hfour])
    rw [heq]

private theorem fixedPoints_map_subtype
    {K W : Type u} [Group K] [Group W] [MulDistribMulAction K W]
    (X : Subgroup K) (B : Subgroup X) :
    FixedPoints.subgroup (B.map X.subtype) W = FixedPoints.subgroup B W := by
  ext w
  constructor
  · intro hw b
    exact hw ⟨(b : K),Subgroup.mem_map_of_mem X.subtype b.property⟩
  · intro hw b
    obtain ⟨c,hc,heq⟩ := b.property
    have hh := hw ⟨c,hc⟩
    change (c : K) • w = w at hh
    change (b : K) • w = w
    rw [← heq]
    exact hh

public theorem eight_six_cost_four_relative_double_sl2
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (_hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
      (action : P →* MulAut (V ⧸ Z.subgroupOf V)),
      (∀ mover : P, ∀ point : V,
        action mover (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  mover.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      (⊤ : Subgroup (V ⧸ Z.subgroupOf V)) =
        SectionOne.actionClosure action.range (V ⧸ Z.subgroupOf V)
          (FixedPoints.subgroup ((S.subgroupOf P).map action.rangeRestrict)
            (V ⧸ Z.subgroupOf V)) →
      let B := ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a).subgroupOf P).map
        action.rangeRestrict
      let F := ⁅SectionOne.oddCore action.range,B⁆
      Nonempty ((F ⊔ B : Subgroup action.range) ≃* (SL2Two × SL2Two)) ∧
        Nat.card (commutatorAction F (V ⧸ Z.subgroupOf V)) = 16 := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel hgenerate
  let _ := hW
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let W := V ⧸ Z.subgroupOf V
  let X := action.range
  let B := (A.subgroupOf P).map action.rangeRestrict
  let Bauto := (A.subgroupOf P).map action
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ P := hAE.trans geom.group_le
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ _
  have hBmap : B.map X.subtype = Bauto := by
    rw [Subgroup.map_map]
    rfl
  have hBsub : Bauto.subgroupOf X = B := by
    rw [← hBmap]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  obtain ⟨helemAuto,hBautoCard,hproperAuto⟩ := eight_six_cost_four_action_profile
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hcost hN hW action haction hkernel
  let _ := helemAuto
  have helem : IsElementaryAbelian 2 B := by
    rw [← hBsub]
    exact IsElementaryAbelian.subgroupOf (Subgroup.map_le_range action (A.subgroupOf P))
  let _ := helem
  have hBcard : Nat.card B = 4 := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective,hBmap]
    exact hBautoCard
  have hBfixed : FixedPoints.subgroup Bauto W = FixedPoints.subgroup B W := by
    rw [← hBmap,fixedPoints_map_subtype]
  have hfull : (FixedPoints.subgroup B W).index = 8 := by
    rw [← hBfixed]
    exact eight_six_cost_four_full_fixed_index ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
        hQ hcost hN hW action haction hkernel
  have hproper : ∀ t ∈ B, t ≠ 1 → (FixedPoints.subgroup (Subgroup.zpowers t) W).index = 4 := by
    intro t ht htne
    have htAuto : (t:MulAut W) ∈ Bauto := hBmap ▸ Subgroup.mem_map_of_mem X.subtype ht
    have htAutoNe : (t:MulAut W) ≠ 1 := fun heq => htne (Subtype.ext heq)
    have hh := hproperAuto t htAuto htAutoNe
    have hf := fixedPoints_map_subtype X (Subgroup.zpowers t) (W := W)
    rw [MonoidHom.map_zpowers] at hf
    rw [← hf]
    exact hh
  have hm := four_actor_minimum B hBcard hfull hproper
  have hSP : S ≤ P := (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  obtain ⟨_,sylow,hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hSnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hsylow,Subgroup.map_subgroupOf_eq_of_le hSP]
  let T := sylow.mapSurjective action.rangeRestrict_surjective
  have hXgen : (⊤ : Subgroup W) = SectionOne.actionClosure X W
      (FixedPoints.subgroup (T : Subgroup X) W) := by
    change (⊤ : Subgroup W) = SectionOne.actionClosure X W
      (FixedPoints.subgroup ((sylow : Subgroup P).map action.rangeRestrict) W)
    rw [hSnative]
    exact hgenerate
  have hfaith : fixingSubgroup X (Set.univ : Set W) = ⊥ := by
    apply bot_unique
    intro actor hactor
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    rw [mem_fixingSubgroup_iff] at hactor
    exact hactor w (Set.mem_univ w)
  have hXcore : pCore 2 X = ⊥ :=
    SectionOne.twoCore_eq_bot_of_fixed_sylow_generation T hfaith hXgen
  have hXeven : Even (Nat.card X) := by
    apply even_iff_two_dvd.mpr
    exact (show 2 ∣ Nat.card B by rw [hBcard]; decide).trans
      (Subgroup.card_subgroup_dvd_card B)
  let _ : Group.IsSolvable P := (edge_local_data ctx.sectionSeven Γ cp).2.2
  have hsetup : SectionOne.Hypotheses X W :=
    ⟨Group.isSolvable_of_surjective action.rangeRestrict_surjective,hXeven,hfaith,hXcore⟩
  have hnonAuto : commutatorAction₂ Bauto W ≠ ⊥ := by
    intro hquad
    have hdouble : ⁅⁅V,A⁆,A⁆ ≤ Z := by
      apply Subgroup.commutator_le.mpr
      intro c hc b hb
      have hcommV : ⁅V,A⁆ ≤ V :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hAP.trans hPV)
      let π : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
      let cV : V := ⟨c,hcommV hc⟩
      let bP : P := ⟨b,hAP hb⟩
      let bB : Bauto := ⟨action bP,Subgroup.mem_map_of_mem action hb⟩
      have hcimage : π cV⁻¹ ∈ commutatorAction Bauto W := by
        rw [Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z A hPV hAP hN action haction]
        exact Subgroup.mem_map_of_mem π (⁅V,A⁆.inv_mem hc)
      have hdelta : (π cV⁻¹)⁻¹ * (bB • π cV⁻¹) ∈ commutatorAction₂ Bauto W :=
        Subgroup.subset_closure ⟨bB,π cV⁻¹,hcimage,rfl⟩
      rw [hquad] at hdelta
      have hone : (π cV⁻¹)⁻¹ * action bP (π cV⁻¹) = 1 := hdelta
      rw [haction,← map_inv,← map_mul] at hone
      have hh := (QuotientGroup.eq_one_iff _).mp hone
      change (c⁻¹)⁻¹ * (b*c⁻¹*b⁻¹) ∈ Z at hh
      simpa only [inv_inv,commutatorElement_def,mul_assoc] using hh
    have hbound := eight_six_nonquadratic_actor_local ctx hcenter hquot hlength hcard
      previous D L Q hprev hD data A le_rfl hdouble
    have hpos : 0 < Nat.card (A ⊓ D : Subgroup G) := Nat.card_pos
    change Nat.card A ≤ 2 * Nat.card (A ⊓ D : Subgroup G) at hbound
    change 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A at hlarge
    omega
  have hnon : commutatorAction₂ B W ≠ ⊥ := by
    rw [← commutatorAction₂_map_actor_subtype X B,hBmap]
    exact hnonAuto
  exact SectionOne.relative_doubleSL2_of_m_two_nonquadratic hsetup B helem
    hBcard.ge hm.1 hm.2 hnon
end Stellmacher.SectionEight
