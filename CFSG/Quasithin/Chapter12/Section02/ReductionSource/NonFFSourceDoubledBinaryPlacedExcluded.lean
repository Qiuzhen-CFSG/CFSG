module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedRudvalisNaturalDual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded
public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.Transitivity

/-!
# Excluding the Rudvalis component from the original doubled binary branch

The normalizer of every native elementary subgroup of order sixty-four is
transitive on its nonidentity elements.  In the original placed component,
normality of the residual and its exact natural--dual marking force every
normalizer element to preserve the union of the two coordinate axes.  The
checked axis obstruction therefore excludes the Rudvalis alternative.

The final theorem applies this exclusion and the independent J4 exclusion to
the original Chapter 12 witnesses, retaining only their maximal-pushing-up
alternative.  Only that joint application assumes the as-yet-unproved J4
cover; the Rudvalis exclusion has no additional source or model premise.

Source: Aschbacher--Smith 4.4.3, pp.622--623, and its original Chapter 12
non-FF doubled-module application; GLS3 Table 5.3r, p.279.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
/-- The complete marked natural--dual geometry is impossible in native Rudvalis. -/
theorem native_rudvalis_geometry_false
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) : False := by
  have hcW : Nat.card D.sourceOrbit = 64 := by
    obtain ⟨_,_,m,_,_,_,hWK,hcard,_⟩ := hg
    let w := m.toMonoidHom.comp (inclusion hWK)
    exact (Nat.card_congr (MonoidHom.ofInjective
      (m.injective.comp (inclusion_injective hWK))).toEquiv).trans hcard
  apply D.native_geometry_false_of_transitivity A K hr e hg
  intro m hWK
  let w := m.toMonoidHom.comp (inclusion hWK)
  let : IsElementaryAbelian 2 w.range :=
    IsElementaryAbelian.of_surjective w.rangeRestrict w.rangeRestrict_surjective
  have hcard : Nat.card w.range = 64 :=
    (Nat.card_congr (MonoidHom.ofInjective
      (m.injective.comp (inclusion_injective hWK))).toEquiv).symm.trans hcW
  exact Rudvalis.BinaryThreeModules.ElementarySixtyFour.normalizer_transitive w.range hcard


/-- The original marked Ru component is impossible with no model-specific premise. -/
theorem sourceOrbit_binary_oddNormalizer_rudvalis_false
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model) : False := by
  exact D.native_rudvalis_geometry_false A K hr e
    (D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
      K hK hcore hr .ru (Or.inr rfl) e)

/-- The native source alternative is excluded once its independent J4 cover holds. -/
theorem binaryPlacedNativeCase_false_of_janko_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (A : Subgroup G) (hc : D.BinaryPlacedNativeCase A) : False := by
  obtain ⟨hu,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hr,hC,hrank,hodd,hl,⟨name,hname,e,hg⟩,hfour,j,hj,f,hf⟩ := hc
  rcases hname with rfl | rfl
  · exact D.native_janko_geometry_false_of_cover hnative A K hr e hg
  · exact D.native_rudvalis_geometry_false A K hr e hg

/-- Original source witnesses now retain only the unchanged pushing-up branch. -/
theorem sourceOrbit_binary_maximal_pushing_up_of_janko_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L := by
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcases⟩ :=
    D.sourceOrbit_binary_native_oddLocal_obstruction h hd hmany hnon F hF hmodel
  refine ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcases.resolve_right
    (D.binaryPlacedNativeCase_false_of_janko_cover hnative A)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

