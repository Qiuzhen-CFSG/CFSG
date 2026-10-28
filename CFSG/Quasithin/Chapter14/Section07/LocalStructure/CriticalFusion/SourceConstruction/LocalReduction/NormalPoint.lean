module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CyclicResidual
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreOddJoin
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.CyclicFixedRank
public import Theory.GroupTheory.PResidual.AbelianQuotient
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.EarlierWeakClosure.Source
/-!
# Normal point residuals before the 14.7.52 classification

Normality of the literal L₁* lifts to relative normality of L₁ in H.
The same normal branch follows when the actual K/O₂(K) is abelian, using
its canonical comparison with O²(H/O₂(H)). The original point action
identifies L₁/O₂(L₁) as cubic. In the normal branch this gives |L₁*| = 3
and R₁* = C_{T*}(L₁*) of index two, without replacing the full star quotient.

Commutator generation gives a fixed-free cubic on every literal U/V₁
section. Each point-core displacement is a module for that cubic and
therefore has even dimension. The original 12.8.4 kernel theorem then
shows that actors with commutators in one line lie in O₂(H). Terminal-edge
transport proves that the actual critical actor Uα* is nontrivial and
centralizes L₁*. The final applications use the source's literal star
normality and abelian-residual antecedents.

Normality also supplies the plane geometry of 12.8.5, discharging the
plane-centralizer premise of the original 14.7.31 weak-closure implication
in the abelian-residual branch. These are preparations for the remaining
solvable exclusions. The equality QQ_H = R₁, the full clauses of 14.7.5(1),
and the residual alternatives through 14.7.52 remain to be established.
No source datum or local-recognition callback is assumed.

Source: Aschbacher–Smith, Lemmas 12.8.4–5 and 14.7.5, printed
pp.850–851 and 1043–1044; 14.7.31, printed p.1055.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

private theorem point_residual_relative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (pResidual 2 ((B).subgroupOf F.H)).map ((B).subgroupOf F.H).subtype =
      (F.Li L 1).subgroupOf F.H := by
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  apply map_injective F.H.subtype_injective
  rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hBH, residual_group h structural,
    map_subgroupOf_eq_of_le hLH]

/-- Normality of the literal star image lifts through the two-core kernel. -/
theorem pointResidual_normal_of_star_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : (star F (F.Li L 1)).Normal) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let A := (F.Li L 1).subgroupOf F.H
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hp : IsPPerfect 2 A := by
    change IsPPerfect 2 ((F.Li L 1).subgroupOf F.H)
    rw [← point_residual_relative h structural]
    exact isPPerfect_embedded_pResidual 2 _
  have hk : IsPGroup 2 (starMap F).ker := by
    rw [starMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkn : (starMap F).ker ≤ normalizer (A : Set F.H) := by
    rw [starMap, QuotientGroup.ker_mk']
    let S : Sylow 2 F.H := T.subtype (F.invariant 1)
    apply le_trans (pCore_isPGroup.le_sylow_of_normal S)
    change ((T : Subgroup G).subgroupOf F.H) ≤
      normalizer ((F.Li L 1).subgroupOf F.H : Set F.H)
    rw [← subgroupOf_normalizer_eq hLH]
    exact fun _ hx => T_normalizes_L₁ h structural hx
  have he := comap_normalizer_map_of_pPerfect (starMap F) A hp hk hkn
  let : (A.map (starMap F)).Normal := hn
  rw [normalizer_eq_top, comap_top] at he
  exact normalizer_eq_top_iff.mp he.symm

/-- An abelian actual residual quotient forces relative point-residual normality. -/
theorem pointResidual_normal_of_abelian_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (ha : IsMulCommutative ((K F) ⧸ pCore 2 (K F))) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let := ha
  let : IsMulCommutative (pResidual 2 (HStar F.H)) :=
    IsMulCommutative.of_comm (fun a b => (residualStarEquiv F).symm.injective
      (by simp only [map_mul, mul_comm]))
  rw [← point_residual_relative h structural]
  have hk : IsPGroup 2 (starMap F).ker := by
    rw [starMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  exact residual_normal_of_p_kernel_abelian_residual (starMap F)
    (QuotientGroup.mk'_surjective _) hk S ((B).subgroupOf F.H)
    (fun _ hx => mem_sup_right hx)

/-- The original point residual has cubic two-core quotient, before classification. -/
theorem pointResidual_core_quotient_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Nat.card ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) = 3 := by
  obtain ⟨f,hf,hk⟩ := exists_point_permutation_action h structural
  let E : pResidual 2 B ≃* F.Li L 1 :=
    (equivMapOfInjective (pResidual 2 B) (B).subtype (B).subtype_injective).trans
      (MulEquiv.subgroupCongr (residual_group h structural))
  let Q := QuotientGroup.congr _ _ E (pCore_map_iso 2 E)
  rw [← Nat.card_congr Q.toEquiv,
    Nat.card_congr (f.pResidualCoreQuotientEquiv hf hk).toEquiv,
    Equiv.Perm.twoResidual_eq_alternating]
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hthree : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  have hcore : pCore 2 (alternatingGroup (Fin 3)) = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hthree.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  rw [hcore, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hc]

/-- Relative normality identifies the point residual image as the same cubic quotient. -/
theorem pointResidual_star_card_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : Nat.card (star F (F.Li L 1)) = 3 := by
  let A := (F.Li L 1).subgroupOf F.H
  let : A.Normal := hn
  let f := (starMap F).subgroupMap A
  have hk : f.ker = pCore 2 A := by
    rw [ker_subgroupMap, starMap, QuotientGroup.ker_mk',
      pCore_subnormal_eq_comap 2 hn.isSubnormal]
    rfl
  have E := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f ((starMap F).subgroupMap_surjective A))
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    let e : A ≃* F.Li L 1 := subgroupOfEquivOfLe
      (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right)
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  exact (Nat.card_congr E.toEquiv).symm.trans hc

/-- The normal point residual generates the entire original H-span by commutators. -/
theorem commutator_U_point_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : ⁅F.U, F.Li L 1⁆ = F.U := by
  let := h.chosen.elementary
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  exact (conjugateSpanBy_eq_commutator_of_seed V F.H (F.Li L 1) (F.Li L 1)
    hLH ((normal_subgroupOf_iff_le_normalizer hLH).mp hn) le_rfl
    (seed_commutator h F)).symm

/-- The original H-span lies in the point residual in the normal branch. -/
theorem U_le_pointResidual_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : F.U ≤ F.Li L 1 := by
  let := h.chosen.elementary
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  rw [← commutator_U_point_of_normal h hn]
  exact le_normalizer_iff_commutator_le_right.mp
    (F.U_le_H.trans ((normal_subgroupOf_iff_le_normalizer hLH).mp hn))

/-- The original point core maps to the core of the original point image. -/
theorem point_core_star_eq_image_core :
    star F (F.Ri L 1) = (star F B).pCoreIn 2 := by
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have he : ((B).subgroupOf F.H).pCoreIn 2 =
      ((B).pCoreIn 2).subgroupOf F.H := by
    apply map_injective F.H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ _ F.H.subtype_injective,
      map_subgroupOf_eq_of_le hBH,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBH)]
  change (((B).pCoreIn 2).subgroupOf F.H).map (starMap F) = _
  have hk : IsPGroup 2 (starMap F).ker := by
    rw [starMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  rw [← he, map_pCoreIn_of_ker_isPGroup (starMap F) hk]
  rfl

/-- In the normal-L₁ branch, R₁* is exactly the Sylow centralizer of L₁*. -/
theorem point_core_star_eq_centralizer_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    star F (F.Ri L 1) = star F (T : Subgroup G) ⊓
      centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  let : (star F (F.Li L 1)).Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_star_card_of_normal h structural hn)
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  let S' : Sylow 2 (HStar F.H) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hs : star F B = star F (F.Li L 1) ⊔ (S' : Subgroup (HStar F.H)) := by
    change ((B).subgroupOf F.H).map (starMap F) = _
    rw [subgroupOf_sup (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right)
      (show (T : Subgroup G) ≤ F.H from F.invariant 1), Subgroup.map_sup]
    rfl
  rw [point_core_star_eq_image_core, hs, core_join_odd_eq_sylow_centralizer _ hp S']
  rfl

/-- The centralizer of the normal cubic has index two in the original star Sylow. -/
theorem point_core_star_index_two_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    (star F (F.Ri L 1)).relIndex (star F (T : Subgroup G)) = 2 := by
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hBH : B ≤ F.H := sup_le hLH hTH
  let f : B →* HStar F.H := (starMap F).comp (inclusion hBH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((starMap F).ker.comap (inclusion hBH))
    rw [show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBH)
  have hrange : f.range = star F B := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨inclusion hBH b,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b.val,hb⟩,rfl⟩
  have hratio := point_image_ratio h structural f hk
  have hRcard : Nat.card (star F (F.Ri L 1)) = Nat.card (pCore 2 (star F B)) := by
    rw [point_core_star_eq_image_core]
    exact card_map_of_injective (star F B).subtype_injective
  rw [hrange, ← hRcard] at hratio
  have hc := pointResidual_star_card_of_normal h structural hn
  let : (star F (F.Li L 1)).Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hthree : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  have htwo : IsPGroup 2 (star F (T : Subgroup G)) :=
    T.isPGroup'.comap_subtype.map (starMap F)
  have hBcard : Nat.card (star F B) = 3 * Nat.card (star F (T : Subgroup G)) := by
    change Nat.card (((B).subgroupOf F.H).map (starMap F)) = _
    rw [subgroupOf_sup hLH hTH, Subgroup.map_sup]
    change Nat.card (star F (F.Li L 1) ⊔ star F (T : Subgroup G) : Subgroup (HStar F.H)) = _
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal
        (hthree.disjoint_of_coprime htwo (by decide : Nat.Coprime 3 2)), hc]
  rw [hBcard] at hratio
  have hRT : star F (F.Ri L 1) ≤ star F (T : Subgroup G) := by
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hindex := relIndex_mul_relIndex (⊥ : Subgroup (HStar F.H)) _ _ bot_le hRT
  simp only [relIndex_bot_left] at hindex
  have hpos := Nat.card_pos (α := star F (F.Ri L 1))
  nlinarith

/-- The actual point core centralizes the cubic image; no quotient model is chosen. -/
theorem point_core_star_centralizes_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    star F (F.Ri L 1) ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  rw [point_core_star_eq_centralizer_of_normal h structural hn]
  exact inf_le_right

/-- Source 14.7.5(5) on every literal U/V₁ section. -/
theorem point_generates_section_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    Representation.BinaryOffender.subspaceCommutator ρ ⊤ ((F.Li L 1).subgroupOf F.H) = ⊤ := by
  have ht : s.imageSpace F.U = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨v, hv⟩ := s.onto (Multiplicative.ofAdd w)
    exact (s.mem_imageSpace_iff _ _).mpr ⟨v, v.property, congrArg Multiplicative.toAdd hv⟩
  have he := s.imageSpace_commutator (F.Li L 1) F.U
    (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right) le_rfl
  rw [commutator_comm, commutator_U_point_of_normal h hn, ht] at he
  exact he.symm

/-- The same generated section retains the literal star marking. -/
theorem point_generates_star_section_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (hσ : σ.comp (starMap F) = ρ) :
    Representation.BinaryOffender.subspaceCommutator σ ⊤ (star F (F.Li L 1)) = ⊤ := by
  rw [Source.star, ← Representation.BinaryOffender.subspaceCommutator_comp_map, hσ]
  exact point_generates_section_of_normal h hn s

/-- The cubic generator is fixed-free on the literal section in the normal branch. -/
theorem exists_fixedFree_cubic_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (hσ : σ.comp (starMap F) = ρ) :
    ∃ z : HStar F.H, orderOf z = 3 ∧ zpowers z = star F (F.Li L 1) ∧
      ∀ v, σ z v = v → v = 0 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hc := pointResidual_star_card_of_normal h structural hn
  let : IsCyclic (star F (F.Li L 1)) := isCyclic_of_prime_card hc
  obtain ⟨z,hz⟩ := (star F (F.Li L 1)).isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (star F (F.Li L 1)))
  refine ⟨z, ?_, hz, ?_⟩
  · rw [← Nat.card_zpowers, hz, hc]
  · apply CyclicFixedRank.fixedFree_of_commutator_eq_top σ z
    rw [hz]
    exact point_generates_star_section_of_normal h hn s σ hσ

/-- The actual reciprocal actor centralizes L₁* in the normal branch,
as in source 14.7.5(4). -/
theorem critical_actor_star_centralizes_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (c : CriticalPath (L := L) F) :
    star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  apply le_trans (map_mono (subgroupOf_mono F.H (critical_le_Ri h structural c)))
  exact point_core_star_centralizes_of_normal h structural hn

/-- Every point-core displacement has even binary rank in the normal-L₁ branch.
This is the no-transvection calculation in the proof of source 14.7.5(1). -/
theorem point_core_displacement_even_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (a : F.H) (ha : (a : G) ∈ F.Ri L 1) :
    Even (Module.finrank (ZMod 2) (ρ a - LinearMap.id).range) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  obtain ⟨z,_,hz,hfix⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
  let r := starMap F a
  have hr : r ∈ centralizer (star F (F.Li L 1) : Set (HStar F.H)) :=
    point_core_star_centralizes_of_normal h structural hn (mem_map_of_mem _ ha)
  let D : Subrepresentation (σ.comp (star F (F.Li L 1)).subtype) := {
    toSubmodule := (σ r - LinearMap.id).range
    apply_mem_toSubmodule g v hv := by
      obtain ⟨w,rfl⟩ := hv
      refine ⟨σ g.val w, ?_⟩
      change σ r (σ g.val w) - σ g.val w = σ g.val (σ r w - w)
      rw [map_sub]
      have hc := congrArg (fun f : Module.End (ZMod 2) W => f w)
        ((show Commute g.val r from hr g.val g.property).map σ).eq
      simpa only [Module.End.mul_apply] using congrArg (fun v : W => v - σ g.val w) hc.symm }
  have hp : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_star_card_of_normal h structural hn)
  have hd : D.toRepresentation.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfix v.val (congrArg Subtype.val
      (hv ⟨z, hz ▸ (show z ∈ zpowers z from mem_zpowers z)⟩))
  have he := Representation.BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup
    D.toRepresentation Nat.prime_three (by decide) hp hd
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at he
  have heq : σ r = ρ a := congrArg (fun τ : Representation (ZMod 2) F.H W => τ a) hσ
  change 2 ∣ Module.finrank (ZMod 2) (σ r - LinearMap.id).range at he
  rw [heq] at he
  exact even_iff_two_dvd.mpr he

/-- A point-core actor with commutators in an ambient line acts trivially on
U/V₁ in the normal-L₁ branch. This supplies the literal section calculation
needed for the subsequent critical-pair argument. -/
theorem point_actor_trivial_of_line_commutator_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) (hA : A ≤ F.Ri L 1)
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2)
    (a : F.H) (ha : (a : G) ∈ A) : ρ a = 1 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hcard : Nat.card (s.imageSpace C) ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : G)) he)))
    exact hm.trans (hs.trans hC)
  have hdim : Module.finrank (ZMod 2) (s.imageSpace C) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    by_contra hn
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) (s.imageSpace C) by omega)
    omega
  have hr : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 1 :=
    (Submodule.finrank_mono
      (s.displacement_range_le_imageSpace_of_commutator_le A C hc a ha)).trans hdim
  have he := point_core_displacement_even_of_normal h structural hn s a (hA ha)
  have hz : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range = 0 := by
    obtain ⟨n,hn⟩ := he
    omega
  have hz' : (ρ a - LinearMap.id).range = ⊥ := Submodule.finrank_eq_zero.mp hz
  exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp hz')

/-- Relative L₁-normality gives the plane-normalizer bound and the two
geometric clauses used by the later source weak-closure argument. -/
theorem normal_point_plane_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    F.Gi 2 ≤ normalizer (L : Set G) ∧
      (∀ g : G, F.Vi 2 ≤ conjugate V g → conjugate V g = V) ∧
      ∀ g : G, g ∉ seedNormalizer (normalizer (L : Set G)) V →
        primeRank 2 (V ⊓ conjugate V g : Subgroup G) ≤ 1 := by
  let := h.chosen.elementary
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hplanes : ∀ W : Subgroup G, W ≤ V → Nat.card W = 4 →
      ∃ l ∈ L, conjugate W l = F.Vi 2 := by
    intro W hW hc
    apply h.subspace_transitive W (F.Vi 2) hW (F.le_seed 2)
    rw [hc, F.card 2 (by decide)]
    rfl
  have he := F.normal_Li_one_geometry_of_ambient_natural h.naturalMarking
    h.rank.1 h.residual rfl hn
    (fun g hg => h.seed_TI structural g⁻¹ ((normalizer (L : Set G)).inv_mem hg))
    (h.seed_normalizer_le structural uniqueness) hplanes
    (fun i _ _ g hg => h.flag_transporter F i g hg)
  exact ⟨(he.1 2 (by decide) (by decide)).2.2.1,
    (he.1 2 (by decide) (by decide)).2.2.2.2, he.2⟩

/-- The literal plane centralizer lies in M in the normal-L₁ source branch. -/
theorem plane_centralizer_le_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) :=
  (Subgroup.centralizer_le_normalizer _).trans (normal_point_plane_geometry h structural hn).1

/-- Apply the actual original 14.7.31 implication in the abelian residual
branch, discharging its plane-centralizer premise from the original marking. -/
theorem point_weakClosure_of_abelian_residual
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (ha : IsMulCommutative ((K F) ⧸ pCore 2 (K F))) :
    ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ L ⊔ (T : Subgroup G) ∧
      L ⊔ (T : Subgroup G) ≤
        normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ∧
      normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ≤
        normalizer (L : Set G) := by
  let := h.chosen.elementary
  exact (source_theorem14731 structural G T L V d h F hab
    (plane_centralizer_le_of_point_normal h structural
      (pointResidual_normal_of_abelian_residual h structural ha))).1

/-- Escape supplies the exact kernel of every literal binary section, using
the original 12.8.4 theorem rather than a residual-model assumption. -/
theorem section_action_kernel_eq_core_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ρ.ker = pCore 2 F.H := by
  let := h.chosen.elementary
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have he : ρ.ker = (F.localTildeAction F.H le_rfl).ker := by
    ext a
    exact (s.action_mem_ker_iff a).trans
      (F.mem_localTildeAction_ker_iff F.H le_rfl a).symm
  rw [he]
  exact F.localKernel_eq_pCore h.source.simpleQTKE L (normalizer (L : Set G)) F.H
    (by decide) h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique structural uniqueness).2 (h.seed_centralizer_le structural uniqueness)
    h.centralizer_L (F.H_mem_Hz (by decide) L (normalizer (L : Set G)) hescape)

/-- The normal cubic detects point-core actors in the literal two-core,
once the earlier-source escape has supplied the exact section kernel. -/
theorem point_actor_in_core_of_line_commutator_of_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) (hA : A ≤ F.Ri L 1)
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2) :
    A ≤ F.H.pCoreIn 2 := by
  intro a ha
  have haH : a ∈ F.H := ((pCoreIn_le 2 B).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))) (hA ha)
  have he := point_actor_trivial_of_line_commutator_of_normal h structural hn s
    A C hA hc hC ⟨a,haH⟩ ha
  exact mem_map_of_mem F.H.subtype
    ((section_action_kernel_eq_core_of_escape h structural hescape s).le
      (show (⟨a,haH⟩ : F.H) ∈ ρ.ker from he))

/-- Source 14.7.5's even-displacement argument forces the reciprocal actor
to have nontrivial star image on the actual critical path. -/
theorem critical_star_nontrivial_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (c : CriticalPath (L := L) F) : star F c.Uα ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hz
  have hAH : c.Uα ≤ F.H := (critical_le_Ri h structural c).trans
    ((pCoreIn_le 2 B).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [CriticalFusion.Source.star, Subgroup.map_eq_bot_iff, starMap,
        QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    have haH : a ∈ F.H := hAH ha
    have hqa : (⟨a,haH⟩ : F.H) ∈ pCore 2 F.H := by
      obtain ⟨a',ha',he⟩ := hαQ ha
      exact (show a' = ⟨a,haH⟩ from Subtype.ext he) ▸ ha'
    exact (s.action_mem_ker_iff ⟨a,haH⟩).mp (core_le_action_kernel h s hqa) u hu
  obtain ⟨g,hUg,hHg,hAR⟩ := exists_terminal_edge_transport h structural c
  let f := (MulAut.conj g).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hm := map_mono (f := f) hcomm
    change c.Uα.map f = F.U at hUg
    rw [map_commutator,hUg] at hm
    exact hm
  have hC : Nat.card C ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact (show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)).le
  have hAQ := point_actor_in_core_of_line_commutator_of_normal h structural hescape hn
    s A C hAR hc hC
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective,hHg]
  exact critical_span_not_le_reciprocal_core c
    ((map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
      (hAQ.trans_eq hQmap.symm))

/-- The normal-point branch constructs a genuine critical actor,
centralizing the original cubic and with nonzero original star image.
The only escape input is the full earlier 12.2.13 theorem. -/
theorem exists_critical_geometry_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ∃ c : CriticalPath (L := L) F, c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨c⟩ := exists_criticalPath h hab (h.flag_escape F previous) structural uniqueness
  exact ⟨c,critical_le_Ri h structural c,
    critical_star_nontrivial_of_point_normal h hab structural (h.flag_escape F previous) hn c,
    critical_actor_star_centralizes_of_point_normal h structural hn c⟩

/-- An abelian literal K/O₂(K) supplies the normality needed for the
preceding critical-pair construction. This does not exclude that branch. -/
theorem exists_critical_geometry_of_abelian_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (ha : IsMulCommutative ((K F) ⧸ pCore 2 (K F))) :
    ∃ c : CriticalPath (L := L) F, c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) :=
  exists_critical_geometry_of_point_normal h hab structural previous
    (pointResidual_normal_of_abelian_residual h structural ha)

/-- Apply the normal-point reductions to the literal star-normality
antecedent of 14.7.5. The source equality Q* = R₁* and the full residual
classification are separate obligations and are not asserted here. -/
theorem normal_point_structure_of_star_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hstar : (star F (F.Li L 1)).Normal) :
    Nat.card (star F (F.Li L 1)) = 3 ∧
      star F (F.Ri L 1) = star F (T : Subgroup G) ⊓
        centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
      (star F (F.Ri L 1)).relIndex (star F (T : Subgroup G)) = 2 ∧
      ⁅F.U,F.Li L 1⁆ = F.U ∧
      ∃ c : CriticalPath (L := L) F, c.Uα ≤ F.Ri L 1 ∧
        star F c.Uα ≠ ⊥ ∧
        star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  have hn := pointResidual_normal_of_star_normal h structural hstar
  exact ⟨pointResidual_star_card_of_normal h structural hn,
    point_core_star_eq_centralizer_of_normal h structural hn,
    point_core_star_index_two_of_normal h structural hn,
    commutator_U_point_of_normal h hn,
    exists_critical_geometry_of_point_normal h hab structural previous hn⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
