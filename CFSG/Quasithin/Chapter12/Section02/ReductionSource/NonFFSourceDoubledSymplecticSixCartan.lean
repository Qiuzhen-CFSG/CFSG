module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticSixCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticOddAction
public import Theory.GroupAction.PerfectCentralQuotient
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF

/-!
# The original A₆ Cartan bound and odd-local reduction

The same seed marking descends the normalizer action through the center
of L/O₂(L). If its image preserved the natural S₆ action, the actual
inverse-conjugator from MarkedDoubled would intertwine the two seeds.
Their nonisomorphism therefore gives the diagram-moving hypothesis of
the binary Cartan theorem. The full quotient action has parameter one.

The final application removes the Cartan alternative from the original
Hall-kernel reduction, retaining both actual odd-local configurations.
Their exclusion, Hall faithfulness and the upper bound on w remain.
Source: Aschbacher--Smith 7.3.4--5 and 4.4.3--14,
printed pp.699 and 619--625, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE ChapterE.Section06.FixedPointBounds Chapter4 Chapter4.Section04
open Chapter7.NormalizedSource AlternatingSix.ShadowLocal
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_six_quotientAction_nPrime_le_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    nPrime (normalizerPCoreQuotientAction L).range ≤ 1 := by
  let := h.quasisimple
  let := D.elementary
  obtain ⟨m⟩ := hmodel
  let q := m.groupEquiv.toMonoidHom.comp D.componentHom
  let r := m.groupEquiv.toMonoidHom.comp D.componentQuotientHom
  have hr : Function.Surjective r := m.groupEquiv.surjective.comp D.componentQuotientHom_surjective
  have hk : r.ker = center (L ⧸ pCore 2 L) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)),MonoidHom.comap_bot] at hh
    exact hh
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective r hr)
  have he (x : L ⧸ pCore 2 L) : e (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) x) = r x := rfl
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  let a := f.comp (normalizerPCoreQuotientAction L)
  have ha (g : normalizer (L : Set G)) (l : L) :
      a g (q l) = q (L.normalizerMonoidHom g l) := by
    change f (normalizerPCoreQuotientAction L g) (r (QuotientGroup.mk' (pCore 2 L) l)) = _
    rw [←he,MulAut.centralQuotientAction_apply,he]
    change r (quotientAut (pCore 2 L) (L.normalizerMonoidHom g)
      (QuotientGroup.mk' (pCore 2 L) l)) = _
    rw [quotientAut_apply_mk]
    rfl
  let E := (seedCoordinates D).symm.trans m.linearEquiv
  have hE : ∀ l v, E (doubledSeedAction L V D.normalizes l v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (q l) (E v) := by
    intro l v
    obtain ⟨w,rfl⟩ := (seedCoordinates D).surjective v
    rw [←seedCoordinates_action D]
    simp only [E,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    exact m.intertwines (D.componentHom l) w
  obtain ⟨t,ht,_,hne,_⟩ :=
    @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  let g : normalizer (L : Set G) := ⟨t⁻¹,inv_mem (D.sylow_normalizes_component ht)⟩
  have hout : ¬ a.range ≤ natural := by
    intro hin
    apply DoubledSymplecticSixCartan.nonnatural_of_seed_inequivalent
      (doubledSeedAction L V D.normalizes) q E hE
      (doubledTwist L t (D.sylow_normalizes_component ht)) (a g) (ha g) _ (hin ⟨g,rfl⟩)
    rintro ⟨b,hb⟩
    apply hne
    refine ⟨Representation.Equiv.mk b ?_⟩
    intro l
    exact LinearMap.ext (hb l)
  have hinner : AlternatingSix.ShadowLocal.inner ≤ a.range := by
    rintro b ⟨x,rfl⟩
    obtain ⟨z,rfl⟩ := e.surjective x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L)) z
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
    refine ⟨inclusion L.le_normalizer l,?_⟩
    change f (normalizerPCoreQuotientAction L (inclusion L.le_normalizer l)) = _
    rw [normalizerPCoreQuotientAction_inner,MulAut.centralQuotientAction_conj]
  have hA : (normalizerPCoreQuotientAction L).range.map f = a.range := by
    rw [MonoidHom.range_comp]
  have hmap : Function.Injective (f.subgroupMap (normalizerPCoreQuotientAction L).range) := by
    intro x y he
    exact Subtype.ext (hf (congrArg Subtype.val he))
  obtain ⟨w⟩ := nPrime_spec (X := (normalizerPCoreQuotientAction L).range)
  have hb := (w.map (f.subgroupMap _) (f.subgroupMap_surjective _)
    (hmap.comp w.cyclicGroup.subtype_injective)).le_nPrime
  rw [hA] at hb
  exact hb.trans (DoubledSymplecticSixCartan.automorphism_subgroup_nPrime_le_one _ hinner hout)

theorem sourceOrbit_six_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
      ∃ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      1 < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
    ((∃ J P : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
      PushLE L (oddActorResidual L A) J ∧
      IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))) := by
  exact (D.sourceOrbit_six_cartan_or_oddLocal_obstruction h hd hmany hnon hmodel).resolve_left
    (not_lt_of_ge (D.sourceOrbit_six_quotientAction_nPrime_le_one h hd hmodel))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
