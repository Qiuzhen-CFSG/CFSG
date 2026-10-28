module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The original left parabolic and residual in 14.7.70

The natural L-action restricts onto the stabilizer of the original point z.
The residual/Sylow supplement puts L ∩ N_G(V₁) inside L₁T. Its action on
V/⟨z⟩ is onto GL₂(2), and its kernel is a two-group: the natural action
kernel and the point-stabilizer displacement kernel are both two-groups.
The projective-line equivalence GL₂(2) ≃ S₃ therefore identifies the actual
quotient by O₂(L₁T). Together with the independently proved right quotient
and prescribed intersection, this constructs the genuine Goldschmidt triple.

T normalizes the original embedded point residual L₁, so adjoining T does
not change its two-residual. The same statement is transported through
both subtype maps of the actual left vertex in I, giving a literal
isomorphism O²(left) ≃ L₁ for the chief-factor comparison.

The sole extra premise is the genuine universal Structural1222 implication,
whose existing producer is qt-12-02. No triple, intersection, nontrivial
core or chief-factor count is assumed. The five-chief-factor lower bound
and its source assembly remain with qt-14-07-rechoice-left-chief-factors.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.7.70, printed p.1074 (PDF p.1091); Notation 12.8.2,
printed p.849, and the preceding natural-action setup.
-/

@[expose] public section
noncomputable section
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
theorem T_normalizes_L₁
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
  rw [Li_eq_residual]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ F.H) (pResidual 2 (L ⊓ F.H : Subgroup G)))
  exact (le_inf (d.natural.sylow_normalizes structural)
    ((F.invariant 1).trans F.H.le_normalizer)).trans inf_normalizer_le_normalizer_inf

/-- The intrinsic residual in L₁T embeds as exactly the original L₁. -/
theorem residual_group
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (pResidual 2 (group F L)).map (group F L).subtype = F.Li L 1 := by
  apply embedded_pResidual_join_pGroup _ _ _ T.isPGroup' (T_normalizes_L₁ d structural)
  rw [Li_eq_residual]
  exact isPPerfect_embedded_pResidual 2 (L ⊓ F.H)

private theorem point_normalizer_le_group
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    L ⊓ F.H ≤ group F L := by
  let N := L ⊓ F.H
  let J := N ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf (d.natural.sylow_normalizes structural)
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
theorem exists_left_permutation_action
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
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
      d.natural.chosen.normalizes (d.natural.centralizer_LT structural)
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
def leftQuotientEquiv
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ((group F L) ⧸ pCore 2 (group F L)) ≃* Equiv.Perm (Fin 3) := by
  apply Classical.choice
  obtain ⟨f, hf, hk⟩ := exists_left_permutation_action d structural
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (ker_eq_twoCore_of_surjective_perm_three f hf hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- Restricting the same left actor to I preserves its intrinsic core quotient. -/
theorem quotient_left (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Nonempty (((left c) ⧸ pCore 2 (left c)) ≃* Equiv.Perm (Fin 3)) := by
  let e := subgroupOfEquivOfLe (show group F L ≤ I c from le_sup_left)
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (leftQuotientEquiv d structural)⟩

/-- Both quotient actions and the prescribed intersection now give the genuine triple. -/
theorem triple (c : CriticalPath (L := L) F) (h : Geometry d c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ChapterF.IsGoldschmidtTriple (left c) (right c) :=
  h.triple_of_left_quotient (quotient_left d c structural)

/-- The residual used by a comparison on the left vertex is the original L₁,
with both subtype maps displayed. -/
theorem residual_left (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ((pResidual 2 (left c)).map (left c).subtype).map (I c).subtype = F.Li L 1 := by
  have hm : (left c).map (I c).subtype = group F L :=
    map_subgroupOf_eq_of_le (show group F L ≤ I c from le_sup_left)
  rw [map_embedded_pResidual, hm]
  exact residual_group d structural

/-- An isomorphism with the original L₁, obtained from the displayed
subtype maps rather than from an abstract residual model. -/
def leftResidualEquiv (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    pResidual 2 (left c) ≃* F.Li L 1 := by
  let f := (I c).subtype.comp (left c).subtype
  have hf : Function.Injective f := (I c).subtype_injective.comp (left c).subtype_injective
  have hm : (pResidual 2 (left c)).map f = F.Li L 1 := by
    rw [show f = (I c).subtype.comp (left c).subtype from rfl, ← map_map]
    exact residual_left d c structural
  exact ((pResidual 2 (left c)).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hm)

/-- The residual isomorphism is the literal ambient inclusion. -/
@[simp] theorem leftResidualEquiv_apply (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (x : pResidual 2 (left c)) :
    (leftResidualEquiv d c structural x : G) = (x.val.val : G) := rfl

end LeftChiefFactors
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
