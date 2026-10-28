module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSClassification
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeRecognition
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs.FieldTransport

/-!
# Marking the original nonblock parabolic and both module sections

The nonbinary initial-action theorem identifies the literal central-omega
kernel with O₂(KR). The induced full quotient isomorphism to K* therefore
retains the scalar center. C.2.7's radical-normalizer placement and the
intrinsic SL₃ recognition theorem put the original L-image in a point or
line parabolic residual, without any block hypothesis.

The same linear change of basis transports the natural center and both dual
quotient factors. On the duals the transport is precomposition with the
inverse basis map; this preserves the common quotient marking and actual
actions. NonblockMSConstruction uses these sections to construct MSData
and select the actual secondary component.

Whole-core classification and its third-row selection remain earlier source
obligations; this module proves the original parabolic placement from the
full SL₃ quotient, not the existence of that quotient in every source case.
Source: Aschbacher--Smith C.2.7, C.4.5--7, pp.145--147,152--153,
and original 4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {F : Type} [Field F] [Finite F]

private def starEquivOfKernel {K R : Subgroup G}
    (hR : R ≤ normalizer (K : Set G))
    (hk : starKernel K R = pCore 2 (K ⊔ R : Subgroup G)) :
    (K ⧸ pCore 2 K) ≃* starImage K R K := by
  have hker : (toStarImage K R).ker = pCore 2 K := by
    apply le_antisymm _ (core_le_toStarImage_ker hR)
    have he : (toStarImage K R).ker =
        (pCore 2 (K ⊔ R : Subgroup G)).comap (inclusion (show K ≤ K ⊔ R from le_sup_left)) := by
      ext k
      change toStarImage K R k = 1 ↔ _
      rw [Subtype.ext_iff]
      change QuotientGroup.mk' (starKernel K R) (inclusion le_sup_left k) = 1 ↔ _
      exact (QuotientGroup.eq_one_iff _).trans (by rw [hk]; rfl)
    rw [he]
    exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective _ (inclusion_injective _)⟩
  exact MulEquiv.ofBijective (coreToStar hR)
    ⟨(QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm,coreToStar_surjective hR⟩

omit [Finite G] in
private theorem starEquivOfKernel_mk {K R : Subgroup G}
    (hR : R ≤ normalizer (K : Set G))
    (hk : starKernel K R = pCore 2 (K ⊔ R : Subgroup G)) (k : K) :
    starEquivOfKernel hR hk (QuotientGroup.mk' (pCore 2 K) k) = toStarImage K R k := rfl

omit [Finite G] in
private theorem local_image_star :
    (L.subgroupOf (K c)).map (toStarImage (K c) (c.I.pCoreIn 2)) =
      (starImage (K c) (c.I.pCoreIn 2) L).subgroupOf
        (starImage (K c) (c.I.pCoreIn 2) (K c)) := by
  ext x
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨⟨k,mem_sup_left k.property⟩,hk,rfl⟩
  · intro hx
    obtain ⟨j,hj,hjx⟩ := hx
    refine ⟨⟨j,c.le_component hj⟩,hj,?_⟩
    exact Subtype.ext hjx

/-- The full nonbinary quotient marks the original L-image as one of the
two parabolic residuals. The star kernel is proved equal to the two-core,
so the marking retains the full scalar center, including in degree two. -/
theorem nonblock_linearThree_local_frame
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hn : 1 < n) (hF : Nat.card F = 2^n) [CharP F 2]
    (e₀ : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      (L.subgroupOf (K c)).map
        (linearThreeActor (e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj a))) =
          pointLocalSL F ∨
      (L.subgroupOf (K c)).map
        (linearThreeActor (e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj a))) =
          lineLocalSL F := by
  let C := starImage (K c) (c.I.pCoreIn 2) (K c)
  let R := (starImage (K c) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf C
  let B := (starImage (K c) (c.I.pCoreIn 2) L).subgroupOf C
  have hk : starKernel (K c) (c.I.pCoreIn 2) = pCore 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G) :=
    ms_centralOmega_kernel c D hf n hn hF e₀
  let q := starEquivOfKernel c.block_radical_normalizes hk
  let E := q.symm.trans e₀
  have hB : (L.subgroupOf (K c)).map (toStarImage (K c) (c.I.pCoreIn 2)) = B :=
    local_image_star
  have hspan : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  let : Group.IsPerfect L := hspan ▸ c.c28.span_perfect
  let : Group.IsPerfect (L.subgroupOf (K c)) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe c.le_component).symm.toMonoidHom)
    (subgroupOfEquivOfLe c.le_component).symm.surjective
  let : Group.IsPerfect B := hB ▸ Group.IsPerfect.map (toStarImage (K c) (c.I.pCoreIn 2))
  have hBE : B.map E.toMonoidHom = (L.subgroupOf (K c)).map (linearThreeActor e₀) := by
    rw [←hB,map_map]
    congr 1
    apply MonoidHom.ext
    intro k
    change e₀ (q.symm (toStarImage (K c) (c.I.pCoreIn 2) k)) = _
    rw [←starEquivOfKernel_mk c.block_radical_normalizes hk k]
    exact congrArg e₀ (q.symm_apply_apply _)
  have hBne : B ≠ ⊥ := by
    intro hb
    have hh : (L.subgroupOf (K c)).map (linearThreeActor e₀) = ⊥ := by rw [←hBE,hb,Subgroup.map_bot]
    have hLcore : L ≤ (K c).pCoreIn 2 := by
      intro l hl
      have hzero : linearThreeActor e₀ ⟨l,c.le_component hl⟩ = 1 :=
        mem_bot.mp (hh ▸ mem_map_of_mem _ hl)
      have hcore : (⟨l,c.le_component hl⟩ : K c) ∈ pCore 2 (K c) :=
        (QuotientGroup.eq_one_iff _).mp (e₀.map_eq_one_iff.mp hzero)
      exact mem_map_of_mem _ hcore
    have hnil := ((isPGroup_pCoreIn 2 (K c)).to_le hLcore).isNilpotent
    have hLne : L ≠ ⊥ := by
      intro hbot
      apply c.c28.module_nontrivial
      apply bot_unique
      have hm : W c ≤ L := by simpa only [hspan] using c.c28.module_le
      exact hm.trans hbot.le
    let : Nontrivial L := L.nontrivial_iff_ne_bot.mpr hLne
    exact Group.IsPerfect.not_isNilpotent L hnil
  have hKN : ((K c).subgroupOf c.H).Normal := by
    have he : (K c).subgroupOf c.H = c.K :=
      c.K.comap_map_eq_self_of_injective c.H.subtype_injective
    exact he.symm ▸ c.component_normal
  let := hKN
  have hp := ChapterC.C27Source.star_intersection_placement_of_large_order
    (c.block_source_input hf) (show 40320 < Nat.card C from by
      rw [←Nat.card_congr q.toEquiv,Nat.card_congr e₀.toEquiv,
        Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
      have hq : 4 ≤ Nat.card F := by rw [hF]; exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega)
      have h3 : 64 ≤ Nat.card F ^ 3 := by simpa using Nat.pow_le_pow_left hq 3
      have h2 : 16 ≤ Nat.card F ^ 2 := by simpa using Nat.pow_le_pow_left hq 2
      exact lt_of_lt_of_le (by norm_num : 40320 < 64*(64-1)*(16-1))
        (Nat.mul_le_mul (Nat.mul_le_mul h3 (Nat.sub_le_sub_right h3 1)) (Nat.sub_le_sub_right h2 1)))
  have hBN := c.block_star_L_le_radical_normalizer
  have hNB := hp.2.trans c.block_star_local_normalizes_L
  let B' := B.map E.toMonoidHom
  let R' := R.map E.toMonoidHom
  let : Group.IsPerfect B' := Group.IsPerfect.map E.toMonoidHom
  have hB' : B' ≠ ⊥ := fun he => hBne ((B.map_eq_bot_iff_of_injective E.injective).mp he)
  have hBR : B' ≤ normalizer (R' : Set SL(3,F)) := by
    rw [←map_equiv_normalizer_eq R E]
    exact map_mono hBN
  have hRB : normalizer (R' : Set SL(3,F)) ≤ normalizer (B' : Set SL(3,F)) := by
    rw [←map_equiv_normalizer_eq R E,←map_equiv_normalizer_eq B E]
    exact map_mono hNB
  obtain ⟨a,ha⟩ := Matrix.PSL3.LinearThree.RadicalNormalizer.radical_perfect_normal_frame
    R' B' (hp.1.map_equiv E) hB' hBR hRB hn hF
  refine ⟨a,?_⟩
  have he : (L.subgroupOf (K c)).map
      (linearThreeActor (e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj a))) =
      B'.map (Matrix.HigherLinear.SubspaceTransport.slConj a).toMonoidHom := by
    change _ = (B.map E.toMonoidHom).map _
    rw [hBE,map_map]
    rfl
  rw [he]
  exact ha.imp And.right And.right

omit [Finite G] [Finite F] in
private theorem natural_reframe (a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (g : SL(3,F)) (v : Fin 3 → F) :
    a (Representation.specialLinearNatural 3 g v) =
      Representation.specialLinearNatural 3 (Matrix.HigherLinear.SubspaceTransport.slConj a g) (a v) := by
  symm
  simpa only [Representation.specialLinearNatural_apply,LinearEquiv.symm_apply_apply,Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.toLin'_apply] using Matrix.HigherLinear.SubspaceTransport.slConj_apply a g (a v)

omit [Finite G] [Finite F] in
private theorem dual_reframe (a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (g : SL(3,F)) (v : Module.Dual F (Fin 3 → F)) :
    a.symm.dualMap ((Representation.specialLinearNatural (k := F) 3).dual g v) =
      (Representation.specialLinearNatural (k := F) 3).dual
        (Matrix.HigherLinear.SubspaceTransport.slConj a g) (a.symm.dualMap v) := by
  apply LinearMap.ext
  intro x
  change v ((Representation.specialLinearNatural 3 g⁻¹) (a.symm x)) =
    v (a.symm ((Representation.specialLinearNatural 3
      (Matrix.HigherLinear.SubspaceTransport.slConj a g)⁻¹) x))
  rw [←map_inv]
  apply congrArg v
  apply a.injective
  rw [a.apply_symm_apply]
  simpa only [a.apply_symm_apply] using natural_reframe a g⁻¹ (a.symm x)

/-- One linear change of coordinates simultaneously preserves the actual
natural center and both dual quotient factors while marking the original
local image. No point/line placement is supplied as a premise. -/
theorem exists_reframed_natural_center_sections
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hn : 1 < n) (hF : Nat.card F = 2^n) [CharP F 2]
    (e₀ : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hnat : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e₀)
      (Representation.specialLinearNatural (k := F) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e₀)
      ((Representation.specialLinearNatural (k := F) 3).dual.prod
        (Representation.specialLinearNatural (k := F) 3).dual)) :
    ∃ e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := F) 3) ∧
      HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
        ((Representation.specialLinearNatural (k := F) 3).dual.prod
          (Representation.specialLinearNatural (k := F) 3).dual) ∧
      ((L.subgroupOf (K c)).map (linearThreeActor e) = pointLocalSL F ∨
        (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) := by
  obtain ⟨a,ha⟩ := nonblock_linearThree_local_frame D hf hn hF e₀
  refine ⟨e₀.trans (Matrix.HigherLinear.SubspaceTransport.slConj a),?_,?_,ha⟩
  · exact hnat.transport a.toAddEquiv (fun k v => natural_reframe a (linearThreeActor e₀ k) v)
  · apply hdual.transport (a.symm.dualMap.toAddEquiv.prodCongr a.symm.dualMap.toAddEquiv)
    intro k v
    exact Prod.ext (dual_reframe a (linearThreeActor e₀ k) v.1)
      (dual_reframe a (linearThreeActor e₀ k) v.2)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
