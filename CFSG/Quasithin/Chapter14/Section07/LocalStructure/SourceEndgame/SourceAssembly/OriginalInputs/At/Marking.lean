module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.PointCommutator

/-!
# Original parabolic marking and four chief factors at G,T

The actual L₁T action on V/V₁ has quotient S₃. Its image in H/O₂(H)
has order 24, so the five-point stabilizer calculation chooses coordinates
with the original R₁ as upper root. The two-residual identifies the marked
Borel. The original section and its commutator dual then give four
noncentral chief factors in the same L₁. Only local structural and A₅
module inputs remain. Source: AS 14.7.64–67, pp.1069–1070.
Final earlier-source discharge remains with qt-d-14775-source.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

namespace LeftChiefFactors

omit [Finite G] in
private theorem Li_eq_residual : F.Li L 1 =
    (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
  simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]
  rfl

include d

/-- T preserves the original point residual, using the earlier 12.2.2 normalization. -/
theorem T_normalizes_L₁_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
  rw [Li_eq_residual]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ F.H) (pResidual 2 (L ⊓ F.H : Subgroup G)))
  exact (le_inf (d.natural.sylow_normalizes_at structural)
    ((F.invariant 1).trans F.H.le_normalizer)).trans inf_normalizer_le_normalizer_inf

/-- The intrinsic residual in L₁T embeds as exactly the original L₁. -/
theorem residual_group_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (pResidual 2 (group F L)).map (group F L).subtype = F.Li L 1 := by
  apply embedded_pResidual_join_pGroup _ _ _ T.isPGroup' (T_normalizes_L₁_at d structural)
  rw [Li_eq_residual]
  exact isPPerfect_embedded_pResidual 2 (L ⊓ F.H)

private theorem point_normalizer_le_group
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    L ⊓ F.H ≤ group F L := by
  let N := L ⊓ F.H
  let J := N ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf (d.natural.sylow_normalizes_at structural)
      ((F.invariant 1).trans F.H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let : (N.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le N.le_normalizer hTN)
  obtain ⟨S, hS⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal (N.subgroupOf J)
  have hs := congrArg (fun B : Subgroup (N.subgroupOf J) =>
    (B.map (N.subgroupOf J).subtype).map J.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, Subgroup.map_sup, map_embedded_pResidual,
    map_subgroupOf_eq_of_le (show N ≤ J from le_sup_left),
    ← MonoidHom.range_eq_map, range_subtype,
    map_subgroupOf_eq_of_le (show N ≤ J from le_sup_left), hS, subgroupOf_map_subtype] at hs
  apply le_trans hs.symm.le
  apply sup_le
  · rw [show N = L ⊓ F.H from rfl, ← Li_eq_residual]
    exact le_sup_left
  · exact (map_mono inf_le_left).trans (by
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)]
      exact le_sup_right)

/-- The left action is obtained from conjugation on the original natural
module, followed by the quotient by its original fixed point. -/
theorem exists_left_permutation_action_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ f : group F L →* Equiv.Perm (Fin 3),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let := d.natural.chosen.elementary
  let z : Additive V := Additive.ofMul ⟨d.z, (F.le_seed 1) (d.point ▸ mem_zpowers d.z)⟩
  have hz0 : z ≠ 0 := fun he => d.z_ne_one (congrArg (fun v : Additive V => (v.toMul : G)) he)
  let a : MulAut V ≃* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun f => { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := by intro f; ext; rfl
      right_inv := by intro f; ext; rfl
      map_mul' := by intro f g; ext; rfl }
  let seed := F.binarySeedAction L d.natural.chosen.normalizes
  let f₀ := seed.comp (inclusion (group_le_LT : group F L ≤ L ⊔ (T : Subgroup G)))
  let f₁ := a.toMonoidHom.comp f₀
  have hfz (g : group F L) : f₁ g z = z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g : G) * d.z * (g : G)⁻¹ = d.z
    have hc := mem_centralizer_iff.mp (group_centralizes_point d g.property)
      d.z (d.point ▸ mem_zpowers d.z)
    rw [← hc, mul_inv_cancel_right]
  let f : group F L →* Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer z :=
    f₁.codRestrict _ hfz
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨l, hl, he⟩ := d.natural.full_L_action (a.symm b.val)
    have hez := he z.toMul
    have hlz : l * d.z * l⁻¹ = d.z := by
      change l * d.z * l⁻¹ = ((a.symm b.val) z.toMul : G) at hez
      have hb := congrArg (fun v : Additive V => (v.toMul : G)) b.property
      exact hez.trans hb
    have hlH : l ∈ F.H := by
      rw [d.centralizer_eq]
      intro x hx
      have hx' : x = d.z := Set.mem_singleton_iff.mp hx
      subst x
      exact (mul_inv_eq_iff_eq_mul.mp hlz).symm
    refine ⟨⟨l, point_normalizer_le_group d structural ⟨hl, hlH⟩⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact he v.toMul
  have hk : IsPGroup 2 f.ker := by
    have hs : IsPGroup 2 seed.ker := F.binarySeedAction_ker_isPGroup L
      d.natural.chosen.normalizes (d.natural.centralizer_LT_at structural)
    have hfk : f.ker = f₁.ker := MonoidHom.ker_codRestrict _ _ _
    rw [hfk]
    change IsPGroup 2 (a.toMonoidHom.comp f₀).ker
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    change IsPGroup 2 (seed.ker.comap (inclusion
      (group_le_LT : group F L ≤ L ⊔ (T : Subgroup G))))
    exact hs.comap_of_injective _ (inclusion_injective _)
  let q := Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction z
  have hq : Function.Surjective q :=
    Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction_surjective z
  have hqk : IsPGroup 2 q.ker := IsElementaryAbelian.isPGroup 2
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel z)
  have hdim : Module.finrank (ZMod 2)
      (Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace z) = 2 := by
    have hd := (Theory.LinearAlgebra.BinaryFivePointStabilizer.line z).finrank_quotient_add_finrank
    have hv : Module.finrank (ZMod 2) (Additive V) = 3 :=
      d.natural.naturalMarking.coordinates.finrank_eq.trans (by simp)
    change Module.finrank (ZMod 2)
      (Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace z) +
        Module.finrank (ZMod 2) (Theory.LinearAlgebra.BinaryFivePointStabilizer.line z) =
          Module.finrank (ZMod 2) (Additive V) at hd
    rw [finrank_span_singleton hz0, hv] at hd
    omega
  let b : Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace z ≃ₗ[ZMod 2]
      (Fin 2 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  let e := (BinaryLinear.SmallParabolicLevi.linearGroupCongr b).trans
    BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
  let g := e.toMonoidHom.comp (q.comp f)
  refine ⟨g, e.surjective.comp (hq.comp hf), ?_⟩
  dsimp only [g]
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker]
  exact hqk.comap_of_ker_isPGroup f hk

/-- The first isomorphism theorem identifies the actual left two-core quotient. -/
def leftQuotientEquiv_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ((group F L) ⧸ pCore 2 (group F L)) ≃* Equiv.Perm (Fin 3) := by
  apply Classical.choice
  obtain ⟨f, hf, hk⟩ := exists_left_permutation_action_at d structural
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (ker_eq_twoCore_of_surjective_perm_three f hf hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩


end LeftChiefFactors
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
local notation "B" => (group F L)

private theorem source_kernel : IsPGroup 2 (sourceActorMap d).ker := by
  change IsPGroup 2 (d.qH.comp (inclusion group_le_H)).ker
  rw [← MonoidHom.comap_ker, d.qH_ker]
  exact (isPGroup_pCoreIn 2 F.H).comap_subtype.comap_of_injective _
    (inclusion_injective group_le_H)

/-- Core lifting counts the original image without choosing an upper marking. -/
theorem source_image_ratio_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Nat.card (sourceActorMap d).range = 6 * Nat.card (pCore 2 (sourceActorMap d).range) := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let I : Subgroup ChapterJ.S5 := f.range
  let g : B →* I := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hk : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact source_kernel d
  have hquot : Nat.card (B ⧸ pCore 2 B) = 6 := by
    rw [Nat.card_congr (leftQuotientEquiv_at d structural).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hquot, g.card_pCore_of_ker_isPGroup hg hk] at hc
  have hc' := card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv] at hc'
  apply Nat.mul_left_cancel (Nat.card_pos (α := g.ker))
  change Nat.card g.ker * Nat.card I = Nat.card g.ker * (6 * Nat.card (pCore 2 I))
  nlinarith [hc, hc']

private theorem eight_dvd_source_image : 8 ∣ Nat.card (sourceActorMap d).range := by
  let TH : Sylow 2 F.H := T.subtype (F.invariant 1)
  let P : Sylow 2 ChapterJ.S5 := TH.mapSurjective d.qH_surjective
  have hP : (P : Subgroup ChapterJ.S5) ≤ (sourceActorMap d).range := by
    rw [Sylow.coe_mapSurjective, sourceActorMap_range]
    apply map_mono
    exact subgroupOf_mono F.H (le_sup_right : (T : Subgroup G) ≤ B)
  have hc : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    decide +kernel
  rw [← hc]
  exact card_dvd_of_le hP

/-- The actual parabolic image has order24 and its two-core has order4. -/
theorem source_image_card_unmarked_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Nat.card (sourceActorMap d).range = 24 ∧
      Nat.card (pCore 2 (sourceActorMap d).range) = 4 := by
  have hc := source_image_ratio_at d structural
  have h8 := eight_dvd_source_image d
  have hd : Nat.card (sourceActorMap d).range ∣ 120 := by
    convert (sourceActorMap d).range.card_subgroup_dvd_card using 1
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := (sourceActorMap d).range)).exists_card_eq
  have hb := Nat.le_of_dvd (by decide : 0 < 120) hd
  have hnle : n ≤ 4 := by
    by_contra h
    have hp : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hn] at hc
    norm_num at hp
    omega
  interval_cases n <;> norm_num at hn <;> simp_all

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08 LocalGeometry.Preparation
open Theory.SpecificGroups.Alternating
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
local notation "B" => (group F L)

private theorem source_core_image_unmarked :
    ((F.Ri L 1).subgroupOf F.H).map d.qH = (sourceActorMap d).range.pCoreIn 2 := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let I : Subgroup ChapterJ.S5 := f.range
  let g : B →* I := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hk : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact source_kernel d
  have hp : (pCore 2 B).map g = pCore 2 I := by
    rw [← g.comap_pCore_of_ker_isPGroup hg hk]
    apply map_comap_eq_self
    rw [g.range_eq_top_of_surjective hg]
    exact le_top
  have he : ((pCore 2 B).map (B).subtype).subgroupOf F.H =
      (pCore 2 B).map (inclusion group_le_H) := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      exact ⟨b, hb, Subtype.ext hba⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  change (((pCore 2 B).map (B).subtype).subgroupOf F.H).map d.qH = _
  rw [he, map_map]
  change (pCore 2 B).map f = (pCore 2 I).map I.subtype
  rw [← hp, map_map]
  rfl

private theorem root_remark (k : ChapterJ.S5) :
    root (d.remark k).naturalQuotient =
      (root d.naturalQuotient).map (MulAut.conj k).toMonoidHom := by
  rw [root, root, map_map]
  rfl

/-- Align the upper root by changing only the natural target coordinates. -/
theorem exists_upperMarking_remark_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ k : ChapterJ.S5, UpperMarking (d.remark k) := by
  obtain ⟨i, hi⟩ := FivePointTwentyFour.exists_eq_stabilizer
    (sourceActorMap d).range (source_image_card_unmarked_at d structural).1
  obtain ⟨j, hj⟩ := borel_eq_even_stabilizer d.naturalQuotient
  have hN : normalizer d.naturalQuotient = MulAction.stabilizer ChapterJ.S5 j := by
    rw [normalizer, hj, FiveBorelCentralFactor.even_stabilizer_normalizer]
  let k : ChapterJ.S5 := Equiv.swap j i
  have hNI : (normalizer d.naturalQuotient).map (MulAut.conj k).toMonoidHom =
      (sourceActorMap d).range := by
    rw [hN, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hi]
    congr 1
    exact Equiv.swap_apply_left j i
  have hk : IsPGroup 2 (MulAut.conj k).toMonoidHom.ker := by
    rw [(MulAut.conj k).toMonoidHom.ker_eq_bot_iff.mpr (MulAut.conj k).injective]
    exact IsPGroup.of_bot
  refine ⟨k, ?_⟩
  change ((F.Ri L 1).subgroupOf F.H).map d.qH = root (d.remark k).naturalQuotient
  rw [root_remark, ← normalizer_twoCore,
    map_pCoreIn_of_ker_isPGroup _ hk, hNI]
  exact source_core_image_unmarked d
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08 LocalGeometry.Preparation
open Matrix.SpecialLinearGroup
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- One conjugator, used for all subsequent source applications. -/
def upperConjugator_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) : ChapterJ.S5 :=
  Classical.choose (exists_upperMarking_remark_at d structural)

/-- One coordinated datum, with the original quotient map and source action. -/
def upperRemark_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Data T L V F W := d.remark (upperConjugator_at d structural)

theorem upperRemark_upperMarking_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    UpperMarking (upperRemark_at d structural) :=
  Classical.choose_spec (exists_upperMarking_remark_at d structural)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors
open Matrix.SpecialLinearGroup
open Theory.SpecificGroups.Alternating
open LocalGeometry.Preparation
open scoped IsMulCommutative

private theorem marking_range (r : ChapterJ.L2FourAction) :
    (markingHom r).range = alternatingGroup (Fin 5) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (r.marking g).property
  · intro hx
    obtain ⟨g, hg⟩ := r.marking.surjective ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩

private theorem borel_eq_root_normalizer_inf (r : ChapterJ.L2FourAction) :
    borel r = alternatingGroup (Fin 5) ⊓ Subgroup.normalizer (root r : Set ChapterJ.S5) := by
  have hp : (Subgroup.normalizer (root r : Set ChapterJ.S5)).comap (markingHom r) = B0 := by
    change (Subgroup.normalizer (U0.map (markingHom r) : Set ChapterJ.S5)).comap (markingHom r) = B0
    rw [comap_normalizer_eq_of_le_range (map_le_range (markingHom r) U0)]
    rw [comap_map_eq_self_of_injective (markingHom_injective r)]
  calc
    borel r = B0.map (markingHom r) := rfl
    _ = ((Subgroup.normalizer (root r : Set ChapterJ.S5)).comap (markingHom r)).map
        (markingHom r) := congrArg (fun B : Subgroup SL => B.map (markingHom r)) hp.symm
    _ = _ := by rw [map_comap_eq, marking_range]

private theorem root_normalizer_eq (r : ChapterJ.L2FourAction) :
    Subgroup.normalizer (root r : Set ChapterJ.S5) = normalizer r := by
  apply le_antisymm _ (normalizer_le_root_normalizer r)
  intro g hg
  change g ∈ Subgroup.normalizer (borel r : Set ChapterJ.S5)
  rw [borel_eq_root_normalizer_inf]
  apply inf_normalizer_le_normalizer_inf
  constructor
  · rw [Subgroup.normalizer_eq_top]
    trivial
  · exact (Subgroup.normalizer (root r : Set ChapterJ.S5)).le_normalizer hg

private theorem root_card (r : ChapterJ.L2FourAction) : Nat.card (root r) = 4 := by
  rw [Nat.card_congr (rootCoordinates r).toEquiv]
  change Nat.card F = 4
  rw [Nat.card_eq_fintype_card, card_field]

private theorem normalizer_card (r : ChapterJ.L2FourAction) : Nat.card (normalizer r) = 24 := by
  obtain ⟨i, hi⟩ := borel_eq_even_stabilizer r
  have hN : normalizer r = MulAction.stabilizer ChapterJ.S5 i := by
    rw [normalizer, hi, FiveBorelCentralFactor.even_stabilizer_normalizer]
  have hindex : (MulAction.stabilizer ChapterJ.S5 i).index = 5 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hc := (MulAction.stabilizer ChapterJ.S5 i).card_mul_index
  have hS : Nat.card ChapterJ.S5 = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hindex, hS] at hc
  rw [hN]
  omega

private theorem normalizer_residual (r : ChapterJ.L2FourAction) :
    (pResidual 2 (normalizer r)).map (normalizer r).subtype = borel r := by
  have hBN : borel r ≤ normalizer r := (borel r).le_normalizer
  have hB : borel r = alternatingGroup (Fin 5) ⊓ normalizer r := by
    obtain ⟨i, hi⟩ := borel_eq_even_stabilizer r
    rw [normalizer, hi, FiveBorelCentralFactor.even_stabilizer_normalizer]
  have hp : IsPPerfect 2 (borel r) := by
    have hp0 : IsPPerfect 2 B0 := rankOneBorel_isPPerfect
      (by rw [Nat.card_eq_fintype_card, card_field])
    exact hp0.of_surjective (B0.equivMapOfInjective (markingHom r)
      (markingHom_injective r)).toMonoidHom
      (B0.equivMapOfInjective (markingHom r) (markingHom_injective r)).surjective
  apply le_antisymm
  · rw [hB]
    refine le_inf ?_ (map_subtype_le _)
    have h := map_pResidual_le 2 (normalizer r).subtype
    rwa [Equiv.Perm.twoResidual_eq_alternating] at h
  · have hp' : IsPPerfect 2 ((borel r).subgroupOf (normalizer r)) :=
      hp.of_surjective (subgroupOfEquivOfLe hBN).symm.toMonoidHom
        (subgroupOfEquivOfLe hBN).symm.surjective
    have h := map_mono (f := (normalizer r).subtype)
      (le_pResidual_of_isPPerfect ((borel r).subgroupOf (normalizer r)) hp')
    rwa [map_subgroupOf_eq_of_le hBN] at h

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
local notation "B" => (group F L)

private theorem source_map_node (S : Subgroup B) :
    ((S.map (B).subtype).subgroupOf F.H).map d.qH = S.map (sourceActorMap d) := by
  have he : (S.map (B).subtype).subgroupOf F.H = S.map (inclusion group_le_H) := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      exact ⟨b, hb, Subtype.ext hba⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  rw [he, map_map]
  rfl

private theorem source_core_image (mark : UpperMarking d) :
    (pCore 2 B).map (sourceActorMap d) = root d.naturalQuotient := by
  have he := source_map_node d (pCore 2 B)
  change ((F.Ri L 1).subgroupOf F.H).map d.qH =
    (pCore 2 B).map (sourceActorMap d) at he
  rw [← he]
  exact mark

private theorem source_map_kernel_isPGroup : IsPGroup 2 (sourceActorMap d).ker := by
  change IsPGroup 2 (d.qH.comp (inclusion group_le_H)).ker
  rw [← MonoidHom.comap_ker, d.qH_ker]
  exact (isPGroup_pCoreIn 2 F.H).comap_subtype.comap_of_injective _
    (inclusion_injective group_le_H)

private theorem source_image_card_marked
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (mark : UpperMarking d) : Nat.card (sourceActorMap d).range = 24 := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let I : Subgroup ChapterJ.S5 := f.range
  let g : B →* I := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hk : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact source_map_kernel_isPGroup d
  have hp : (pCore 2 B).map g = pCore 2 I := by
    rw [← g.comap_pCore_of_ker_isPGroup hg hk]
    apply map_comap_eq_self
    rw [g.range_eq_top_of_surjective hg]
    exact le_top
  have hm : (pCore 2 I).map I.subtype = root d.naturalQuotient := by
    rw [← hp, map_map]
    exact source_core_image d mark
  have hpc : Nat.card (pCore 2 I) = 4 := by
    calc
      Nat.card (pCore 2 I) = Nat.card ((pCore 2 I).map I.subtype) :=
        (card_map_of_injective I.subtype_injective).symm
      _ = 4 := hm ▸ root_card d.naturalQuotient
  have hquot : Nat.card (B ⧸ pCore 2 B) = 6 := by
    rw [Nat.card_congr (leftQuotientEquiv_at d structural).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hquot, g.card_pCore_of_ker_isPGroup hg hk, hpc] at hc
  have hc' := card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv] at hc'
  apply Nat.mul_left_cancel (Nat.card_pos (α := g.ker))
  change Nat.card g.ker * Nat.card I = Nat.card g.ker * 24
  nlinarith [hc, hc']

/-- The earlier upper-root marking already forces both required Borel images. -/
public theorem compatibleBorel_of_upperMarking_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (mark : UpperMarking d) : CompatibleBorel d := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let N := normalizer d.naturalQuotient
  have hle : f.range ≤ N := by
    have h := le_normalizer_map (H := pCore 2 B) f
    have hcore : (pCore 2 B).map f = root d.naturalQuotient := source_core_image d mark
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, hcore,
      root_normalizer_eq] at h
    exact h
  have heq : f.range = N := eq_of_le_of_card_ge hle (by
    calc
      Nat.card N = 24 := normalizer_card d.naturalQuotient
      _ ≤ Nat.card f.range := (source_image_card_marked d structural mark).ge)
  let q : B →* N := f.codRestrict N (fun b => heq ▸ MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  have hq : Function.Surjective q := by
    intro n
    obtain ⟨b, hb⟩ := (show n.val ∈ f.range from heq.symm ▸ n.property)
    exact ⟨b, Subtype.ext hb⟩
  have hres : (pResidual 2 B).map f = borel d.naturalQuotient := by
    calc
      (pResidual 2 B).map f = ((pResidual 2 B).map q).map N.subtype := by
        rw [map_map]
        rfl
      _ = (pResidual 2 N).map N.subtype := by rw [map_pResidual_of_surjective 2 q hq]
      _ = borel d.naturalQuotient := normalizer_residual d.naturalQuotient
  refine ⟨?_, heq⟩
  rw [← residual_group_at d structural, source_map_node]
  exact hres


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08 ResidualNormalizer Rechoice.Goldschmidt
open Chapter13.Section03.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d
/-- The original core duality and Borel action give four factors in the literal L₁. -/
theorem exists_residual_four_chief_factors_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (five : OriginalAlternatingFiveModules1332At T L) :
    ∃ s : NoncentralChiefRefinement.ChiefSeries (F.Li L 1),
      s.head = ⊥ ∧ s.last = ⊤ ∧ 4 ≤ s.noncentralTwoCount := by
  let d' := LeftChiefFactors.BorelRefinements.upperRemark_at d structural
  have mark := LeftChiefFactors.BorelRefinements.upperRemark_upperMarking_at d structural
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d' d'.sectionCentralizer_from_flag
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  obtain ⟨t,_,_,_,_,h0,h1,ht⟩ := ChiefFactors.exists_original_four_refinement d' s
    (LeftChiefFactors.BorelRefinements.compatibleBorel_of_upperMarking_at d' structural mark)
    d'.sectionCentralizer_from_flag (d'.natural.sylow_normalizes_at structural)
    (d'.U_core_commutator_eq_point_of_original_modules_at five)
  exact ⟨t,h0,h1,ht⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
