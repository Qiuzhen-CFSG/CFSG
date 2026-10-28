module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.PointAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Geometry

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Assembly
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Core
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The original point parabolic at the same G,T

Restrict the original natural action to the point stabilizer and its quotient by the fixed point. The residual/Sylow supplement gives surjectivity, and local structural kernel control identifies the literal quotient by its two-core with S₃.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem group_le_H : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ F.H :=
  sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
omit [Finite G] in
private theorem group_le_LT : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
  sup_le ((F.Li_le L 1).trans (inf_le_left.trans le_sup_left)) le_sup_right
omit [Finite G] in
private theorem group_centralizes_point : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ centralizer (F.Vi 1 : Set G) :=
  group_le_H.trans (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))

variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
omit [Finite G] in
private theorem Li_eq_residual : F.Li L 1 =
    (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
  simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]
  rfl

include h

/-- T preserves the original point residual, using the earlier 12.2.2 normalization. -/
theorem T_normalizes_L₁_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
  rw [Li_eq_residual]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ F.H) (pResidual 2 (L ⊓ F.H : Subgroup G)))
  exact (le_inf (h.sylow_normalizes_at structural)
    ((F.invariant 1).trans F.H.le_normalizer)).trans inf_normalizer_le_normalizer_inf

/-- The intrinsic residual in L₁T embeds as exactly the original L₁. -/
theorem residual_group_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (pResidual 2 ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G))).map ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)).subtype = F.Li L 1 := by
  apply embedded_pResidual_join_pGroup _ _ _ T.isPGroup' (T_normalizes_L₁_at h structural)
  rw [Li_eq_residual]
  exact isPPerfect_embedded_pResidual 2 (L ⊓ F.H)

private theorem point_normalizer_le_group_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    L ⊓ F.H ≤ (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) := by
  let N := L ⊓ F.H
  let J := N ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf (h.sylow_normalizes_at structural)
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

/-- The point action is obtained from conjugation on the original natural
module, followed by the quotient by its original fixed point. -/
theorem exists_point_permutation_action_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ f : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 3),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  obtain ⟨z₀, hz₀, hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hcentral := F.H_eq_centralizer (by decide) z₀ hpoint
  let := h.chosen.elementary
  let z : Additive V := Additive.ofMul ⟨z₀, (F.le_seed 1) (hpoint ▸ mem_zpowers z₀)⟩
  have hz0 : z ≠ 0 := fun he => hz₀ (congrArg (fun v : Additive V => (v.toMul : G)) he)
  let a : MulAut V ≃* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun f => { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := by intro f; ext; rfl
      right_inv := by intro f; ext; rfl
      map_mul' := by intro f g; ext; rfl }
  let seed := F.binarySeedAction L h.chosen.normalizes
  let f₀ := seed.comp (inclusion (group_le_LT : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ L ⊔ (T : Subgroup G)))
  let f₁ := a.toMonoidHom.comp f₀
  have hfz (g : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) : f₁ g z = z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g : G) * z₀ * (g : G)⁻¹ = z₀
    have hc := mem_centralizer_iff.mp (group_centralizes_point (F := F) (L := L) g.property)
      z₀ (hpoint ▸ mem_zpowers z₀)
    rw [← hc, mul_inv_cancel_right]
  let f : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) →* Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer z :=
    f₁.codRestrict _ hfz
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨l, hl, he⟩ := h.full_L_action (a.symm b.val)
    have hez := he z.toMul
    have hlz : l * z₀ * l⁻¹ = z₀ := by
      change l * z₀ * l⁻¹ = ((a.symm b.val) z.toMul : G) at hez
      have hb := congrArg (fun v : Additive V => (v.toMul : G)) b.property
      exact hez.trans hb
    have hlH : l ∈ F.H := by
      rw [hcentral]
      intro x hx
      have hx' : x = z₀ := Set.mem_singleton_iff.mp hx
      subst x
      exact (mul_inv_eq_iff_eq_mul.mp hlz).symm
    refine ⟨⟨l, point_normalizer_le_group_at h structural ⟨hl, hlH⟩⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact he v.toMul
  have hk : IsPGroup 2 f.ker := by
    have hs : IsPGroup 2 seed.ker := F.binarySeedAction_ker_isPGroup L
      h.chosen.normalizes (h.centralizer_LT_at structural)
    have hfk : f.ker = f₁.ker := MonoidHom.ker_codRestrict _ _ _
    rw [hfk]
    change IsPGroup 2 (a.toMonoidHom.comp f₀).ker
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    change IsPGroup 2 (seed.ker.comap (inclusion
      (group_le_LT : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ≤ L ⊔ (T : Subgroup G))))
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
      h.naturalMarking.coordinates.finrank_eq.trans (by simp)
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
def pointQuotientEquiv_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) ⧸ pCore 2 ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G))) ≃* Equiv.Perm (Fin 3) := by
  apply Classical.choice
  obtain ⟨f, hf, hk⟩ := exists_point_permutation_action_at h structural
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (ker_eq_twoCore_of_surjective_perm_three f hf hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
