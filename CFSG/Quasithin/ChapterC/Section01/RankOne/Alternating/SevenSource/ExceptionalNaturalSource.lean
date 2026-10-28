module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalNaturalOrbit
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Source
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The original natural A₅ source belongs to the local class

The actual natural coordinates prove reducedness, full residual movement,
and the exact fixed kernel. The rank-one quotient gives minimal parabolicity,
so the natural Baumann theorem constructs its Sylow and alpha conclusions.
The natural orbit supplies the original alpha closure. These facts identify
the literal local kernel and moved group, including any central fixed alpha
summand, and construct C.1.17 membership without geometric callbacks.

Source: Aschbacher–Smith C.1.21(4), C.1.24 and B.6.10, pp.117,128–131.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource
open ChapterB ChapterB.QuasisimpleSource
universe u
variable {H : Type u} [Group H] [Finite H]

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hn hp
  let := hn
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := A)]
  exact solvableResidual_le_of_solvable_quotient N

/-- The actual natural module, its centralizer quotient and Thompson
movement construct the original local-class inclusion. -/
theorem exceptional_natural_inLocalClass
    (F : BinaryField) (hF : 3 < Nat.card F.Carrier)
    (T : Sylow 2 H) (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (q : H →* SL(2,F.Carrier)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set H)) (hk2 : IsPGroup 2 q.ker)
    (hfit : generalizedFitting H = pCore 2 H)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ centralizer (W : Set H))
    (p : Additive W ≃ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (he : ∀ (g : H) (v : Additive W),
      p (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        specialLinearNatural 2 (q g) (p v)) :
    GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T : Subgroup H) ≤ pResidual 2 H ⊔ baumann (T : Subgroup H)
        from le_sup_right)) := by
  let A := SL(2,F.Carrier)
  let α := NormalElementaryQuotient.representation W q hq hk
  let : Group.IsPerfect A := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hF
  let : Nontrivial A := by
    let t := Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F.Carrier)
    refine ⟨⟨t,1,?_⟩⟩
    intro ht
    have hh := congrArg (fun g : A => g.val 0 1) ht
    simp [t,Matrix.SpecialLinearGroup.transvection_coe] at hh
  have hres : (pResidual 2 H).map q = ⊤ := by
    rw [map_pResidual_of_surjective 2 q hq,(pResidual_eq_top_iff 2 A).mpr perfect_twoPerfect]
  have he' (a : A) (v : Additive W) :
      p (α a v) = linearNatural F 2 a (p v) := by
    obtain ⟨g,rfl⟩ := hq a
    change p (α (q g) v) = specialLinearNatural 2 (q g) (p v)
    rw [←he g v]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W q hq hk g v
  have hW : IsPReduced 2 W := by
    refine ⟨inferInstance,inferInstance,?_⟩
    let c : (H ⧸ centralizer (W : Set H)) ≃* A :=
      (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq)
    apply (map_eq_bot_iff_of_injective (f := c.toMonoidHom) _ c.injective).mp
    rw [pCore_map_iso 2 c,Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot]
  have hfix : fixedSpace α ((pResidual 2 H).map q) = ⊥ := by
    rw [hres]
    apply bot_unique
    intro v hv
    have hpv : p v ∈ (linearNatural F 2).invariants := by
      intro a
      rw [←he']
      exact congrArg p (hv ⟨a,mem_top a⟩)
    have hz := (ExtensionConsequences.linearNatural_invariants F (by decide : 2 ≤ 2)).le hpv
    exact p.injective (hz.trans p.map_zero.symm)
  have hpk : p.toLinearMap.ker = fixedSpace α ((pResidual 2 H).map q) := by
    rw [hfix]
    exact LinearMap.ker_eq_bot.mpr p.injective
  have hmove : ⁅W,pResidual 2 H⁆ = W := by
    have hi : α.IsIrreducible := ExtensionConsequences.irreducible_of_equiv
      ({groupEquiv := MulEquiv.refl A,linearEquiv := p,intertwines := he'} :
        ActionEquiv α (linearNatural F 2))
      (ExtensionConsequences.linearNatural_irreducible F (by decide : 2 ≤ 2))
    have ht : NormalElementaryQuotient.commutatorSpace W (pResidual 2 H) = ⊤ := by
      rw [NormalElementaryQuotient.commutatorSpace_eq W q hq hk,hres]
      exact subspaceCommutator_top_eq_top_of_faithful_irreducible α
        (NormalElementaryQuotient.representation_injective W q hq hk) hi
    apply le_antisymm (commutator_le_left W _) ?_
    intro w hw
    change Additive.ofMul (⟨w,hw⟩ : W) ∈ NormalElementaryQuotient.commutatorSpace W (pResidual 2 H)
    exact ht.symm ▸ (Submodule.mem_top : Additive.ofMul (⟨w,hw⟩ : W) ∈
      (⊤ : Submodule (ZMod 2) (Additive W)))
  have hP := rankOne_minimal_of_twoKernel F q hq hk2 T
  obtain ⟨hB,ha⟩ := RankOneBaumann.natural_baumann_sylow_and_alpha T hP W hW hJ
    q hq hk p.toLinearMap p.surjective he' hpk
  have halpha : thompsonAlpha (T : Subgroup H) ≤ W ⊔
      (thompsonAlpha (T : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) := by
    conv_lhs => rw [ha]
    exact sup_le le_sup_right (inf_le_left.trans le_sup_left)
  have horbit := Alternating.SevenSource.natural_le_alpha_closure T W q hq p he
  have hgen := pResidual_sup_sylow_eq_top T
  exact exceptional_inLocalClass_of_span F hF T W W q hq hk hk2 hfit hB
    (Alternating.SevenSource.exceptional_localKernel (T : Subgroup H) W (pResidual 2 H)
      hgen horbit halpha)
    (Alternating.SevenSource.exceptional_localV_commutator (T : Subgroup H) W (pResidual 2 H)
      hgen horbit halpha hmove) p he

end CFSG.Quasithin.ChapterC.RankOne.SevenSource
