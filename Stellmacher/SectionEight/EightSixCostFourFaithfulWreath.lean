module
public import Stellmacher.SectionEight.EightSixCostFourFullModuleCard
public import Stellmacher.SectionOne.NineCoreSixteenWreath
public import Theory.Representation.FaithfulSixteenPGroupNine
public import Stellmacher.UniqueMaximalContainingMap
public import Stellmacher.UniqueMaximalContainingTransport

/-!
# The full faithful cost-four image is the regular wreath product

The actual next-stabilizer action on Vnext/Znext has full image isomorphic
to SL₂(2) wreath C₂. The selected cost-four hypotheses and the exact supplied
quotient action, normality witness and Sylow-fixed generation are retained.
The ordinary quotient by the next two-core is identified by a separate
kernel theorem; this result only concerns the literal faithful image.

The relative bounded-(1.6) classification produces a subgroup of order 36,
with elementary four actor and odd commutator subgroup of order nine. The
actual two-residual image is an odd prime-power group and equals the odd
core of the full image. Faithfulness on the full elementary module of order
sixteen forces that odd core to have order nine. The projected edge Sylow
supplements it, and the native PSet unique-maximal property descends through
the surjection. The previously proved nine-core sixteen-module recognition
then identifies the full group with the regular wreath product.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), printed
p.44, the cost-four promotion after bounded (1.6). No full faithful model,
ordinary action kernel, or core-free selected geometric subgroup is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u
public theorem eight_six_cost_four_faithful_wreath
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
      Nonempty (action.range ≃* SL2TwoWreathC2) := by
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
  let q : P →* X := action.rangeRestrict
  let B := (A.subgroupOf P).map q
  let O := SectionOne.oddCore X
  let F := ⁅O,B⁆
  have hq : Function.Surjective q := action.rangeRestrict_surjective
  have hker : pCore 2 P ≤ q.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkernel
  have hBmap : B.map X.subtype = (A.subgroupOf P).map action := by
    rw [Subgroup.map_map]
    rfl
  obtain ⟨helemAuto,hBautoCard,_⟩ := eight_six_cost_four_action_profile
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hcost hN hW action haction hkernel
  let _ := helemAuto
  have hBsub : ((A.subgroupOf P).map action).subgroupOf X = B := by
    rw [← hBmap]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have helem : IsElementaryAbelian 2 B := by
    rw [← hBsub]
    exact IsElementaryAbelian.subgroupOf (Subgroup.map_le_range action (A.subgroupOf P))
  let _ := helem
  have hBcard : Nat.card B = 4 := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective,hBmap]
    exact hBautoCard
  have hWcard : Nat.card W = 16 := (eight_six_cost_four_full_module_card
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hcost hN hW action haction hkernel hgenerate).1
  obtain ⟨e⟩ := (eight_six_cost_four_relative_double_sl2 ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
      hN hW action haction hkernel hgenerate).1
  have hsl : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hFBcard : Nat.card (F ⊔ B : Subgroup X) = 36 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,hsl]
  let _ : O.Normal := pPrimeCore_normal
  have hFO : F ≤ O := Subgroup.commutator_le_left _ _
  have hFodd : Nat.Coprime 2 (Nat.card F) :=
    (pPrimeCore_coprime_card (p := 2) (G := X)).of_dvd_right (Subgroup.card_dvd_of_le hFO)
  have hcop : Nat.Coprime (Nat.card F) (Nat.card B) := by
    rw [hBcard]
    exact hFodd.symm.pow_right 2
  have hdis : F ⊓ B = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes F B
    (Subgroup.normalizer_commutator_ge_right _ _)
  rw [hdis,Subgroup.card_bot,hFBcard,hBcard] at hprod
  have hFcard : Nat.card F = 9 := by omega
  have hlocal := (edge_local_data ctx.sectionSeven Γ cp).2
  have hPset := (pFamily_iff_pSet _ _ _).mp hlocal.1
  obtain ⟨prime,hprime,hodd,hres⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    S (sectionThreeHypotheses ctx.sectionSeven) P hPset hlocal.2 q hker
  let _ : Fact prime.Prime := ⟨hprime⟩
  let R := BenderSuzuki.External.hktPResidual 2 X
  let _ : R.Normal := BenderSuzuki.External.hktPResidual_normal
  have hRimage : (twoResidualSubgroup P).map q = R := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual',hktPResidual_map_of_surjective' q hq]
  have hRp : IsPGroup prime R := hRimage ▸ hres
  have hRodd : Nat.Coprime 2 (Nat.card R) := by
    obtain ⟨n,hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact (hodd.pow).coprime_two_left
  have hRO : R ≤ O := le_sSup ⟨inferInstance,hRodd⟩
  let qR := QuotientGroup.mk' R
  have hquotP : IsPGroup 2 (X ⧸ R) := BenderSuzuki.External.hktPResidual_quotient_isPGroup
  have hOP : IsPGroup 2 (O.map qR) := hquotP.to_subgroup _
  have hOodd : Nat.Coprime 2 (Nat.card (O.map qR)) :=
    (pPrimeCore_coprime_card (p := 2) (G := X)).of_dvd_right (Subgroup.card_map_dvd O qR)
  have hObot : O.map qR = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases hOP.card_eq_or_dvd with hone | hdiv
    · exact hone
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hOodd) hdiv)
  have hOR : O = R := le_antisymm (by
    have hh := (Subgroup.map_eq_bot_iff (f := qR) (H := O)).mp hObot
    simpa only [qR,QuotientGroup.ker_mk'] using hh) hRO
  have hOp : IsPGroup prime O := hOR ▸ hRp
  let _ : FaithfulSMul O W := ⟨by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    exact hab⟩
  have hOcard : Nat.card O = 9 :=
    (Representation.card_nine_of_faithful_sixteen_pGroup hOp hWcard
      (hFcard ▸ Subgroup.card_dvd_of_le hFO)).2
  have hSP : S ≤ P := (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  obtain ⟨_,sylow,hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hSnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hsylow,Subgroup.map_subgroupOf_eq_of_le hSP]
  let T := sylow.mapSurjective hq
  have hXgen : (⊤ : Subgroup W) = SectionOne.actionClosure X W
      (FixedPoints.subgroup (T : Subgroup X) W) := by
    change (⊤ : Subgroup W) = SectionOne.actionClosure X W
      (FixedPoints.subgroup ((sylow : Subgroup P).map q) W)
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
  have hXeven : Even (Nat.card X) := even_iff_two_dvd.mpr
    ((show 2 ∣ Nat.card B by rw [hBcard]; decide).trans (Subgroup.card_subgroup_dvd_card B))
  let _ : Group.IsSolvable P := hlocal.2
  have hsetup : SectionOne.Hypotheses X W :=
    ⟨Group.isSolvable_of_surjective hq,hXeven,hfaith,hXcore⟩
  have hproper : (T : Subgroup X) ≠ ⊤ := by
    intro htop
    have hcore : (⊤ : Subgroup X) ≤ pCore 2 X := le_sSup ⟨inferInstance,htop ▸ T.isPGroup'⟩
    have htrivial : (⊤ : Subgroup X) = ⊥ := bot_unique (hcore.trans_eq hXcore)
    have hBbot : B = ⊥ := bot_unique (le_top.trans_eq htrivial)
    rw [hBbot,Subgroup.card_bot] at hBcard
    omega
  have huniq : IsUniqueMaximalContaining (sylow : Subgroup P) ⊤ :=
    native_uniqueMaximalContaining P (sylow : Subgroup P) (by rw [hsylow]; exact hPset.2)
  have hTuniq : IsUniqueMaximalContaining (T : Subgroup X) ⊤ :=
    uniqueMaximalContaining_map_of_ne_top q hq (sylow : Subgroup P) huniq hproper
  have hsupp : O ⊔ (T : Subgroup X) = ⊤ :=
    (SectionThree.pSet_surjective_odd_supplement S P (sectionThreeHypotheses ctx.sectionSeven)
      hPset hlocal.2 q hq hker T).symm
  exact SectionOne.nineCore_sixteen_wreath hsetup T hsupp hTuniq hWcard hOcard B helem hBcard
end Stellmacher.SectionEight
