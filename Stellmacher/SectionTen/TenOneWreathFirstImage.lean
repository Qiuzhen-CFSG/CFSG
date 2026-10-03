module
public import Stellmacher.SectionTen.TenOneTransvectionCases
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Stellmacher.SectionNine.NineSevenModelInputs
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# The first-module kernel in the wreath alternative of (10.1)

Under the actual order-thirty-two terminal module, wreath local quotient,
and order-eight endpoint intersection furnished by (9.5), the intersection
of the first module with the terminal core is exactly the intersection of
the two endpoint modules. The actor is assumed to have order-two displacement
only on the literal terminal quotient V/Z.

The middle core maps to a Sylow subgroup of order eight and normalizes the
first-module image. If that image had order two, it would equal the cyclic
transvection image and its normalizer would preserve the canonical factor.
The complementary-support theorem for a sixteen-element quotient module
excludes this. The image has order at most four because its kernel contains
the order-eight module intersection. The exact kernel/range cardinal formula
therefore gives image order four and kernel order eight, proving equality.

Source: Stellmacher (10.1), printed p.60/PDF p.50, the paragraph excluding
alternative (5), in `refs/files/stellmacher-n-group.pdf`. This is the first
step of that exclusion; the residual-action contradiction is separate.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

private theorem canonical_actor_image_not_two
    {K W : Type u} [Group K] [Finite K] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction K W]
    (hyp : SectionOne.Hypotheses K W) (a : K) (ha : _root_.IsInvolution a)
    (S C : Subgroup K) (hS : IsPGroup 2 S) (hSlarge : 4 < Nat.card S)
    (hW : Nat.card W = 16) (haC : a ∈ C)
    (hnorm : S ≤ Subgroup.normalizer (C : Set K))
    (hfactor : SectionOne.IsOneSevenFactor (V := W)
      (⁅SectionOne.oddCore K, Subgroup.zpowers a⁆ ⊔ Subgroup.zpowers a)) :
    Nat.card C ≠ 2 := by
  intro hC
  let D := ⁅SectionOne.oddCore K, Subgroup.zpowers a⁆ ⊔ Subgroup.zpowers a
  have hcyclic : C = Subgroup.zpowers a := by
    apply (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haC) ?_).symm
    rw [hC, Nat.card_zpowers, orderOf_eq_prime ha.2 ha.1]
  let _ : (SectionOne.oddCore K).Normal := pPrimeCore_normal
  have hSD : S ≤ Subgroup.normalizer (D : Set K) := by
    intro s hs
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hcyclicMap : (Subgroup.zpowers a).map (MulAut.conj s).toMonoidHom =
        Subgroup.zpowers a := by
      rw [← hcyclic]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm hs)
    have hoddMap : (SectionOne.oddCore K).map (MulAut.conj s).toMonoidHom =
        SectionOne.oddCore K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer_of_normal (Subgroup.mem_top s))
    change D.map (MulAut.conj s).toMonoidHom = D
    dsimp only [D]
    rw [Subgroup.map_sup, Subgroup.map_commutator, hoddMap, hcyclicMap]
  obtain ⟨s, hmove, _⟩ := SectionOne.oneSevenFactor_exists_complementary_two_group_conjugate
    hyp D S hfactor hS hW hSlarge
  apply hmove
  rw [SectionOne.RankOneThreeGroupAssembly.commutatorAction_conjBy]
  have heq : D.conjBy (s : K) = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSD s.property)
  rw [heq]

set_option maxHeartbeats 800000 in
public theorem ten_one_wreath_first_core_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G) (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hlarge : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = 2 ^ 3) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a' =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let C := VAt Γ cp.firstStep
  let Qm := QAt Γ middle
  let Qt := QAt Γ cp.a'
  have hb : 1 < cp.length := by change 1 < ctx.criticalPath.length; rw [ctx.critical_length]; decide
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hCP : C ≤ P := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hQmC : Qm ≤ Subgroup.normalizer (C : Set G) :=
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      middle cp.firstStep ((mem_neighborhood_iff_adjacent Γ).mpr hfirst) default).2.2).trans
        (stabilizer_le_normalizer_v Γ cp.firstStep)
  obtain ⟨alignment, _, hterminalAlign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment, hterminalAlign⟩
  let nativeActor : P := ⟨actor, hCP hactor⟩
  obtain ⟨hN, hW, action, _, hkernel, hinv, _, _, hyp, hfactor⟩ :=
    nine_next_transvection_factor ctx.toAmbientSectionNineContext hb cp.a' horbit nativeActor hindex
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let f := action.rangeRestrict
  let imageC := (C.subgroupOf P).map f
  have hfker : f.ker = pCore 2 P := by rw [MonoidHom.ker_rangeRestrict, hkernel]
  have hQtKer : Qt.subgroupOf P = f.ker := by
    rw [hfker]
    change (Γ.twoCoreAt cp.a').subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hpen : cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = middle := by
    obtain ⟨i, hi, hmid⟩ := hpath
    rw [← hmid]
    apply congrArg cp.path
    apply Fin.ext
    change cp.length - 1 = i.val
    change i.val = 2 at hi
    change ctx.criticalPath.length - 1 = i.val
    have hlen := ctx.critical_length
    omega
  obtain ⟨sylow, hsylow⟩ := nine_nine_terminal_core_image_sylow
    ctx.toAmbientSectionNineContext hb f action.rangeRestrict_surjective hfker
  change (sylow : Subgroup action.range) =
    ((QAt Γ (cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).subgroupOf P).map f at hsylow
  rw [hpen] at hsylow
  have hsylowCard := nine_nine_terminal_core_image_card_eight
    ctx.toAmbientSectionNineContext hb f action.rangeRestrict_surjective hfker hmodel
  change Nat.card (((QAt Γ (cp.path ⟨cp.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).subgroupOf P).map f) = 8 at hsylowCard
  rw [hpen, ← hsylow] at hsylowCard
  have hnormal : (sylow : Subgroup action.range) ≤ Subgroup.normalizer (imageC : Set action.range) := by
    rw [hsylow]
    apply le_trans (Subgroup.map_mono ?_) ((C.subgroupOf P).le_normalizer_map f)
    exact (Subgroup.comap_mono hQmC).trans (C.le_normalizer_comap P.subtype)
  have hactorImage : f nativeActor ∈ imageC := Subgroup.mem_map_of_mem f hactor
  have hactorInv : _root_.IsInvolution (f nativeActor) :=
    ⟨fun heq => hinv.1 (congrArg Subtype.val heq), Subtype.ext hinv.2⟩
  have hdata := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hb cp.a' horbit
  have hZU : Z ≤ U := by
    rw [show Z = ⁅U, Qt⁆ from hdata.2.1.symm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((show Qt ≤ P from by change Γ.twoCoreAt cp.a' ≤ P; rw [Γ.twoCoreAt_def]; exact twoCoreIn_le _).trans
        (stabilizer_le_normalizer_v Γ cp.a'))
  have hWcard : Nat.card W = 16 := by
    have hcount := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,
      show Nat.card Z = 2 from hdata.1, hlarge] at hcount
    change Nat.card W * 2 = 2 ^ 5 at hcount
    omega
  have hnotTwo : Nat.card imageC ≠ 2 := canonical_actor_image_not_two
    hyp (f nativeActor) hactorInv sylow imageC sylow.isPGroup'
      (by rw [hsylowCard]; decide) hWcard hactorImage hnormal hfactor
  have hIle : C ⊓ U ≤ C ⊓ Qt := inf_le_inf_left _
    (neighbor_join_le_core_of_length_gt_one Γ cp hb _)
  have hCcard : Nat.card C = 32 := by
    exact (nine_seven_endpoint_module_card ctx.toLocalContext.toSectionNineLocalContext).trans hlarge
  have hIcard' : Nat.card (C ⊓ U : Subgroup G) = 8 := by
    change Nat.card (U ⊓ C : Subgroup G) = 8 at hIcard
    simpa only [inf_comm] using hIcard
  have hkernelCardLower : 8 ≤ Nat.card (C ⊓ Qt : Subgroup G) :=
    hIcard'.symm ▸ Subgroup.card_le_of_le hIle
  let restriction := f.comp (C.subgroupOf P).subtype
  have hrange : restriction.range = imageC := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let kernelEquiv : restriction.ker ≃ (C ⊓ Qt : Subgroup G) := {
    toFun := fun element => ⟨element.val.val.val, element.val.property,
      show element.val.val ∈ Qt.subgroupOf P from hQtKer ▸ element.property⟩
    invFun := fun element => ⟨⟨⟨element.val, hCP element.property.1⟩, element.property.1⟩,
      show (⟨element.val, hCP element.property.1⟩ : P) ∈ f.ker from
        hQtKer ▸ element.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcount : Nat.card imageC * Nat.card (C ⊓ Qt : Subgroup G) = 32 := by
    rw [← Nat.card_congr kernelEquiv, ← hrange, ← Subgroup.index_ker,
      Subgroup.index_mul_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv, hCcard]
  have himageLower : 2 ≤ Nat.card imageC := by
    have htwo := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hactorImage)
    rw [Nat.card_zpowers, orderOf_eq_prime hactorInv.2 hactorInv.1] at htwo
    exact htwo
  have hkernelCard : Nat.card (C ⊓ Qt : Subgroup G) = 8 := by
    have hdiv : Nat.card imageC ∣ 32 := ⟨Nat.card (C ⊓ Qt : Subgroup G), hcount.symm⟩
    have himageUpper : Nat.card imageC ≤ 4 := by nlinarith
    have himage : Nat.card imageC = 4 := by
      interval_cases h : Nat.card imageC <;> simp_all
    rw [himage] at hcount
    omega
  exact (Subgroup.eq_of_le_of_card_ge hIle (by rw [hIcard', hkernelCard])).symm

end Stellmacher.SectionTen
