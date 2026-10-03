module
public import Stellmacher.SectionTen.TenOneDihedralConfiguration
public import Stellmacher.SectionTen.TenOneLargeActionClassification
public import Stellmacher.SectionOne.OneOmegaSupportPointStabilizer
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Excluding the first-center four-point odd support in Stellmacher (10.1)

For a prescribed first-module actor with terminal quotient displacement of
order four, its actual dihedral residual cannot have support of order four
containing the image of the first center. The supplied quotient normality,
elementary structure, action formula, and exact two-core kernel are retained.

Faithfulness makes a four-point odd support an order-three omega factor.
The local odd prime-power residual theorem (3.3) then puts that factor in
the three-core, so the support-intersection consequence of (1.4) applies.
The middle-edge stabilizer fixes the nonzero first-center image, because
it normalizes the middle center and its index-two terminal-center subgroup.
It therefore normalizes the factor. Generation by that edge and the actual
extracted residual makes the factor normal in the full action range.
Its support is consequently invariant. It contains the entire middle-center
image, whose conjugates generate the terminal quotient, so the quotient
itself has order four. The square of an involution's displacement order is
at most the module order, contradicting the selected displacement order four.

This proves the first support-case contradiction of Stellmacher (10.1),
Journal of Algebra 190 (1997), printed p.63, immediately before (13).
It uses the normality of the selected omega factor directly; the source's
intermediate assertion about the whole residual being elementary abelian
is not needed. No source (13) generation or later classification is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionThree
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem relative_index_of_card
    {G : Type*} [Group G] [Finite G] (U Z C : Subgroup G)
    (hZU : Z ≤ U) (hCU : C ≤ U) [hN : (Z.subgroupOf U).Normal]
    (hcard : QuotientCardEq (C ⊔ Z) Z 4) : Z.relIndex C = 4 := by
  have hsup : C ⊔ Z ≤ U := sup_le hCU hZU
  have hindex : Z.relIndex (C ⊔ Z) = 4 := by
    have hmul := (Z.subgroupOf (C ⊔ Z)).index_mul_card
    have hZcard : Nat.card (Z.subgroupOf (C ⊔ Z)) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ C ⊔ Z from le_sup_right)).toEquiv
    rw [hZcard] at hmul
    change Z.relIndex (C ⊔ Z) * Nat.card Z = Nat.card (C ⊔ Z : Subgroup G) at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hmul.trans hcard)
  have heq := Subgroup.relIndex_sup_right (C.subgroupOf U) (Z.subgroupOf U)
  rw [← Subgroup.subgroupOf_sup hCU hZU, Subgroup.relIndex_subgroupOf hsup,
    Subgroup.relIndex_subgroupOf hCU] at heq
  exact heq ▸ hindex

public theorem ten_one_dihedral_first_support_excluded
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (data : TenOneDihedralConfigurationData ctx middle (actor : G) hactor)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
      QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
              point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))
    (hout : (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4)
    (hfour : Nat.card (commutatorAction
      ((data.raw.F₀.subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map action.rangeRestrict)
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))) = 4)
    (hline : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).map
        (QuotientGroup.mk' ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
          (VAt ctx.Γ ctx.criticalPath.a'))) ≤
      commutatorAction
        ((data.raw.F₀.subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map action.rangeRestrict)
        (VAt ctx.Γ ctx.criticalPath.a' ⧸
          (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))) :
    False := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let W := V ⧸ Z.subgroupOf V
  let X := action.range
  let f := action.rangeRestrict
  let R := (data.raw.F₀.subgroupOf P).map f
  let U := commutatorAction R W
  let seed := ZAt Γ middle
  let L := ZAt Γ cp.firstStep
  let q : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let edge := GAt Γ middle ⊓ P
  let K := (edge.subgroupOf P).map f
  have hshort : 1 < cp.length := by
    change 1 < ctx.criticalPath.length
    rw [ctx.critical_length]
    decide
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  have hkernelRange : pCore 2 P ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict, hkernel]
  have hresimage := nine_local_residual_image_eq_oddCore
    ctx.toLocalContext.toSectionNineLocalContext cp.a' middle (Γ.adjacent_symm hterminal)
      f action.rangeRestrict_surjective hkernelRange
  change ((EAt Γ cp.a').subgroupOf P).map f = SectionOne.oddCore X at hresimage
  have hRodd : R ≤ SectionOne.oddCore X := by
    rw [← hresimage]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P data.residual_le)
  have hyp : SectionOne.Hypotheses X W :=
    (ten_one_large_action_classification ctx action hformula hkernel actor hactor hout hindex).1
  have hOmega := SectionOne.oneOmega_of_odd_four_support hyp R hRodd hfour
  let edgeSylow : Sylow 2 (P ⊓ GAt Γ middle : Subgroup G) := default
  let ambientSylow := sylowTwoAmbient (P ⊓ GAt Γ middle) edgeSylow
  have hlocal := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) edgeSylow
  obtain ⟨p, hp, _, hresP⟩ := pSet_residual_image_is_odd_pGroup
    ambientSylow hlocal.1 P hlocal.2.1 hlocal.2.2.2.1 f hkernelRange
  let _ : Fact p.Prime := ⟨hp⟩
  have hnative : (EAt Γ cp.a').subgroupOf P = twoResidualSubgroup P := by
    rw [EAt, CosetGraphContext.e, Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hOprime : IsPGroup p (SectionOne.oddCore X) := by
    rw [← hresimage, hnative]
    exact hresP
  have hp3 : p = 3 := by
    have hRp := hOprime.to_le hRodd
    rcases hRp.card_eq_or_dvd with hone | hdiv
    · rw [hOmega.2.1] at hone
      omega
    · rw [hOmega.2.1] at hdiv
      exact ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_left hp.ne_one
  have hRcore : R ≤ pCore 3 X := hRodd.trans
    (le_sSup ⟨pPrimeCore_normal, hp3 ▸ hOprime⟩)
  have hseedV : seed ≤ V := by
    change ZAt Γ middle ≤ VAt Γ cp.a'
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨middle, (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm hterminal), rfl⟩
  have hsplit : seed = L ⊔ Z := hopen.center_direct_product.1
  have hLseed : L ≤ seed := by
    rw [hsplit]
    exact le_sup_left
  have hZseed : Z ≤ seed := by
    rw [hsplit]
    exact le_sup_right
  have hLV : L ≤ V := hLseed.trans hseedV
  have hZV : Z ≤ V := hZseed.trans hseedV
  obtain ⟨alignment, _, halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hZtwo : Nat.card Z = 2 := (nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment, halignment⟩).1
  have hseedIndex : Z.relIndex seed = 2 := by
    have hh := (Z.subgroupOf seed).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZseed).toEquiv,
      hZtwo, hopen.center_card] at hh
    change Z.relIndex seed * 2 = 4 at hh
    omega
  have hseedEdge : ⁅seed, edge⁆ ≤ Z :=
    SectionEight.commutator_le_of_normalizing_index_two seed Z edge hseedIndex
      (inf_le_left.trans (stabilizer_le_normalizer_z Γ middle))
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a'))
  have hLtwo : Nat.card L = 2 := nine_next_center_order_of_initial_four
    ctx.toLocalContext.toSectionNineLocalContext
      ((lemma_nine_three_ambient ctx.toAmbientSectionNineContext hshort cp.a
        ⟨1, Γ.act_one _⟩).2)
  have hLne : L ≠ ⊥ := by intro hh; rw [hh, Subgroup.card_bot] at hLtwo; omega
  obtain ⟨zL, hzLne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLne
  let z : G := zL
  have hz : z ∈ L := zL.property
  have hzne : z ≠ 1 := fun hh => hzLne (Subtype.ext hh)
  let point : W := q ⟨z, hLV hz⟩
  have hpointU : point ∈ U := hline (Subgroup.mem_map_of_mem q hz)
  have hpointNe : point ≠ 1 := by
    intro hone
    have hzZ : (⟨z, hLV hz⟩ : V) ∈ Z.subgroupOf V :=
      (QuotientGroup.eq_one_iff _).mp hone
    exact hzne (Subgroup.disjoint_def.mp hopen.center_direct_product.2.1 hz hzZ)
  have hKfix : K ≤ MulAction.stabilizer X point := by
    rintro mover ⟨m, hm, rfl⟩
    change action m (q ⟨z, hLV hz⟩) = q ⟨z, hLV hz⟩
    rw [hformula]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (m : G) * z * (m : G)⁻¹ / z ∈ Z
    have hh : ⁅(m : G), z⁆ ∈ Z := by
      rw [Subgroup.commutator_comm] at hseedEdge
      exact hseedEdge (Subgroup.commutator_mem_commutator hm (hLseed hz))
    simpa only [commutatorElement_def, div_eq_mul_inv] using hh
  have hKnorm : K ≤ Subgroup.normalizer (R : Set X) := hKfix.trans
    (SectionOne.oneOmega_point_stabilizer_le_normalizer hyp R hOmega hRcore
      point hpointU hpointNe)
  have hgen : R ⊔ K = ⊤ := by
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup data.raw.F₀_le_P inf_le_right,
      data.edge_generated, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective f action.rangeRestrict_surjective
  have hnorm : Subgroup.normalizer (R : Set X) = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen]
    exact sup_le R.le_normalizer hKnorm
  let _ : R.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  have hstable (mover : X) (point : W) (hpoint : point ∈ U) : mover • point ∈ U := by
    have hconj : R.conjBy mover = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm ▸ Subgroup.mem_top mover)
    rw [show U = commutatorAction R W from rfl, ← hconj,
      ← SectionOne.RankOneThreeGroupAssembly.commutatorAction_conjBy R mover]
    exact Subgroup.mem_map_of_mem _ hpoint
  have hseedImage : (seed.subgroupOf V).map q ≤ U := by
    rw [hsplit, Subgroup.subgroupOf_sup hLV hZV, Subgroup.map_sup]
    apply sup_le hline
    have hzero : (Z.subgroupOf V).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (f := q) (H := Z.subgroupOf V)).mpr
      rw [QuotientGroup.ker_mk']
    rw [hzero]
    exact bot_le
  let lift := (U.comap q).map V.subtype
  have hVclosure : V = conjugateClosure seed P :=
    SectionEight.eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven Γ
      cp.a' middle ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal))
  have hVlift : V ≤ lift := by
    rw [hVclosure]
    apply (Subgroup.closure_le lift).mpr
    rintro x ⟨mover, b, rfl⟩
    have hm := hstable (f mover) (q ⟨b, hseedV b.property⟩) (hseedImage (Subgroup.mem_map_of_mem q b.property))
    change action mover (q ⟨b, hseedV b.property⟩) ∈ U at hm
    rw [hformula] at hm
    exact ⟨⟨(mover : G) * (b : G) * (mover : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (stabilizer_le_normalizer_v Γ cp.a' mover.property)
        b).mp (hseedV b.property)⟩, hm, rfl⟩
  have hUtop : U = ⊤ := by
    apply top_le_iff.mp
    intro w _
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) w
    obtain ⟨v', hv', heq⟩ := hVlift v.property
    have heq' : v' = v := Subtype.ext heq
    exact heq' ▸ hv'
  have hWfour : Nat.card W = 4 := by
    change Nat.card U = 4 at hfour
    rw [hUtop, Nat.card_congr Subgroup.topEquiv.toEquiv] at hfour
    exact hfour
  let C := Subgroup.zpowers (actor : G)
  have hCP : C ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hCV : ⁅V, C⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hCP.trans hPV)
  have hrelative : Z.relIndex ⁅V, C⁆ = 4 :=
    relative_index_of_card V Z ⁅V, C⁆ hZV hCV hindex
  have hCnative : C.subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCP, MonoidHom.map_zpowers]
    rfl
  have hrank := Subgroup.quotient_conjugation_commutatorAction_card
    P V Z C hPV hCP hN action hformula
  rw [hCnative, MonoidHom.map_zpowers] at hrank
  have hdispFour : Nat.card (commutatorAction (Subgroup.zpowers (action actor)) W) = 4 :=
    hrank.trans hrelative
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  have hpow : (action actor) ^ 2 = 1 := by
    rw [← map_pow, show actor ^ 2 = 1 from
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (actor : G) hactor), map_one]
  have hbound := MulAut.displacement_card_sq_le_card (action actor) hpow
  change Nat.card (commutatorAction (Subgroup.zpowers (action actor)) W) ^ 2 ≤ Nat.card W at hbound
  rw [hdispFour, hWfour] at hbound
  norm_num at hbound

end Stellmacher.SectionTen
