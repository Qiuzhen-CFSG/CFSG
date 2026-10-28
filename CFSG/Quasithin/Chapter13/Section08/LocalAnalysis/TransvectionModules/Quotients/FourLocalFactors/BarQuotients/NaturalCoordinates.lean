module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Bar
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.CubicOrder
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Pair

/-!
# Original natural coordinates on the actual barred local groups

The faithful original natural map identifies the permutation kernel with
C_LT(V). The two quotient-range equivalences therefore identify the actual
bar with its natural permutation image. The supplied S₆ isomorphism forces
that image to be all S₆ by cardinality; it is not assumed to be the natural
marking. The resulting natural marking may differ by an outer automorphism.

The intrinsic Sylow supplement proves LᵢT = N_LT(Vᵢ) for the literal embedded
relative residual. Equivariance then identifies its barred image with the
stabilizer of the actual preimage subspace. Neither a parabolic tag nor an
O₂(LT) bar-kernel hypothesis enters this calculation.

Source: Aschbacher–Smith, Notations 12.2.5(2), 13.2.1 and 13.3.3,
original natural module on printed pp.915–916, and 13.8.6(4), p.948.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
variable {G : Type*} [Group G] {L T V V₁ : Subgroup G}

theorem naturalMap_injective (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : Function.Injective n.naturalMap := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [n.naturalMap_kernel]
  apply le_bot_iff.mp
  intro v hv
  apply Subtype.ext
  have hm : (v : G) ∈ V ⊓ centralizer (L : Set G) := ⟨v.property, hv⟩
  rwa [hfixed] at hm

theorem permutation_ker (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    n.permutation.ker = barKernel (L ⊔ T) V := by
  ext g
  constructor
  · intro hg
    apply mem_centralizer_iff.mpr
    intro v hv
    have he := n.conjugation g ⟨v, hv⟩
    rw [show n.permutation g = 1 from hg, map_one, Module.End.one_apply] at he
    have hh := congrArg Subtype.val (naturalMap_injective n hfixed he)
    change (g : G) * v * (g : G)⁻¹ = v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg
    apply ComponentSieve.SixAndG2.NaturalSix.symmetricAction_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, hv⟩ := n.naturalMap_surjective (Multiplicative.ofAdd w)
    have hc : V.normalizerMonoidHom ⟨g.val, n.normalizes_V g.property⟩ v = v := by
      apply Subtype.ext
      change g.val * v.val * g.val⁻¹ = v.val
      have hz : v.val * g.val = g.val * v.val := mem_centralizer_iff.mp hg v.val v.property
      rw [← hz, mul_inv_cancel_right]
    have he := n.conjugation g v
    rw [hc, hv] at he
    change w = ComponentSieve.SixAndG2.NaturalSix.symmetricAction (n.permutation g) w at he
    simpa only [map_one, Module.End.one_apply] using he.symm

noncomputable def barRangeEquiv (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    (barMap (L ⊔ T) V n.normalizes_V).range ≃* n.permutation.range := by
  letI := barKernel_normal (L ⊔ T) V n.normalizes_V
  exact (barEquivImage (L ⊔ T) V n.normalizes_V).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (permutation_ker n hfixed).symm).trans
      (QuotientGroup.quotientKerEquivRange n.permutation))

theorem barRangeEquiv_apply (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : (L ⊔ T : Subgroup G)) :
    barRangeEquiv n hfixed ((barMap (L ⊔ T) V n.normalizes_V).rangeRestrict g) =
      n.permutation.rangeRestrict g := by
  let := barKernel_normal (L ⊔ T) V n.normalizes_V
  have hb : barEquivImage (L ⊔ T) V n.normalizes_V
      (QuotientGroup.mk' (barKernel (L ⊔ T) V) g) =
        (barMap (L ⊔ T) V n.normalizes_V).rangeRestrict g := by
    apply Subtype.ext
    rfl
  rw [← hb]
  simp only [barRangeEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rfl

theorem permutation_surjective (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    Function.Surjective n.permutation := by
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  exact (Nat.card_congr (barRangeEquiv n hfixed).symm.toEquiv).trans
    (Nat.card_congr e.toEquiv)

noncomputable def naturalBarEquiv (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6) :=
  (barRangeEquiv n hfixed).trans
    ((MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr
      (permutation_surjective n hfixed e))).trans topEquiv)

theorem naturalBarEquiv_apply (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (g : (L ⊔ T : Subgroup G)) :
    naturalBarEquiv n hfixed e ((barMap (L ⊔ T) V n.normalizes_V).rangeRestrict g) =
      n.permutation g := by
  change (barRangeEquiv n hfixed
    ((barMap (L ⊔ T) V n.normalizes_V).rangeRestrict g)).val = _
  rw [barRangeEquiv_apply]
  rfl

/-- Literal relative residual in the ambient group. -/
def sourceResidual (L T X : Subgroup G) : Subgroup G :=
  (pResidual 2 ((L ⊔ T) ⊓ normalizer (X : Set G) : Subgroup G)).map
    ((L ⊔ T) ⊓ normalizer (X : Set G)).subtype

theorem residual_sup_T [Finite G] (n : NaturalSetup L T V V₁)
    (X : Subgroup G) (hTX : T ≤ normalizer (X : Set G)) :
    sourceResidual L T X ⊔ T = (L ⊔ T) ⊓ normalizer (X : Set G) := by
  let P := L ⊔ T
  let M := P ⊓ normalizer (X : Set G)
  have hM : M ≤ P := inf_le_left
  have hs : (n.sylow : Subgroup P) ≤ M.subgroupOf P := by
    rw [n.sylow_eq]
    exact fun g hg => ⟨g.property, hTX hg⟩
  let em : M.subgroupOf P ≃* M := subgroupOfEquivOfLe hM
  have hem : Function.Surjective em.toMonoidHom := em.surjective
  let S : Sylow 2 M := (n.sylow.subtype hs).mapSurjective hem
  have hS : (S : Subgroup M).map M.subtype = T := by
    dsimp only [S]
    rw [Sylow.coe_mapSurjective, map_map, Sylow.coe_subtype]
    change ((n.sylow : Subgroup P).subgroupOf (M.subgroupOf P)).map
      (P.subtype.comp (M.subgroupOf P).subtype) = T
    rw [← map_map, map_subgroupOf_eq_of_le hs, n.sylow_eq,
      map_subgroupOf_eq_of_le (show T ≤ P from le_sup_right)]
  have hh := congrArg (fun B : Subgroup M => B.map M.subtype)
    (pResidual_sup_sylow_eq_top S)
  change (pResidual 2 M).map M.subtype ⊔ T = M
  simpa only [Subgroup.map_sup, hS, ← MonoidHom.range_eq_map, range_subtype] using hh

theorem mem_preimage (n : NaturalSetup L T V V₁)
    (W : Submodule (ZMod 2) Natural) (v : V) :
    v.val ∈ sourceLinePreimage n.naturalMap W ↔ (n.naturalMap v).toAdd ∈ W := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (show w = v from Subtype.ext he) ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

theorem preimage_normalizer (n : NaturalSetup L T V V₁)
    (W : Submodule (ZMod 2) Natural) (g : (L ⊔ T : Subgroup G)) :
    g.val ∈ normalizer (sourceLinePreimage n.naturalMap W : Set G) ↔
      n.permutation g ∈ Representation.BinaryOffender.subspaceStabilizer
        (BinaryPermutation.naturalRepresentation (Fin 6)) W := by
  constructor
  · intro hg w
    obtain ⟨v, hv⟩ := n.naturalMap_surjective (Multiplicative.ofAdd w)
    have hv' : (n.naturalMap v).toAdd = w := hv
    rw [← hv', ← n.conjugation, ← mem_preimage, ← mem_preimage]
    exact ((mem_normalizer_iff.mp hg) v.val).symm
  · intro hg
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      let v : V := ⟨x, map_subtype_le _ hx⟩
      have hp := (mem_preimage n W v).mp hx
      have hc := (hg (n.naturalMap v).toAdd).mpr hp
      rw [← n.conjugation] at hc
      exact (mem_preimage n W _).mpr hc
    · intro hx
      have hv : x ∈ V := (mem_normalizer_iff.mp (n.normalizes_V g.property) x).mpr
        (map_subtype_le _ hx)
      let v : V := ⟨x, hv⟩
      have hc := (mem_preimage n W (V.normalizerMonoidHom
        ⟨g.val, n.normalizes_V g.property⟩ v)).mp hx
      rw [n.conjugation] at hc
      exact (mem_preimage n W v).mpr ((hg _).mp hc)

noncomputable def localBar (n : NaturalSetup L T V V₁) (Li : Subgroup G) :
    Subgroup (barMap (L ⊔ T) V n.normalizes_V).range :=
  ((Li ⊔ T).subgroupOf (L ⊔ T)).map (barMap (L ⊔ T) V n.normalizes_V).rangeRestrict

theorem localBar_map [Finite G] (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (X Li : Subgroup G) (W : Submodule (ZMod 2) Natural)
    (hX : X = sourceLinePreimage n.naturalMap W)
    (hTX : T ≤ normalizer (X : Set G)) (hLi : Li = sourceResidual L T X) :
    (localBar n Li).map (naturalBarEquiv n hfixed e).toMonoidHom =
      Representation.BinaryOffender.subspaceStabilizer
        (BinaryPermutation.naturalRepresentation (Fin 6)) W := by
  have hcomp : (naturalBarEquiv n hfixed e).toMonoidHom.comp
      (barMap (L ⊔ T) V n.normalizes_V).rangeRestrict = n.permutation := by
    apply MonoidHom.ext
    intro g
    exact naturalBarEquiv_apply n hfixed e g
  rw [localBar, map_map, hcomp, hLi, residual_sup_T n X hTX]
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (preimage_normalizer n W g).mp (hX ▸ hg.2)
  · intro ha
    obtain ⟨g, rfl⟩ := permutation_surjective n hfixed e a
    exact ⟨g, ⟨g.property, hX.symm ▸ (preimage_normalizer n W g).mpr ha⟩, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients

end
