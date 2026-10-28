module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceAction
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction

/-!
# LocalAnalysisCentralizersThompsonSourceAction at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersThompsonSourceAction`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

theorem maxElementary_image_bestOffender_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hne : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel_at structural).permutation ≠ ⊥) :
    IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 7))
      ((A.subgroupOf (normalizer (V : Set G))).map
        (E.sourceNormalizerModel_at structural).permutation) := by
  let N := normalizer (V : Set G)
  let W := V.subgroupOf N
  let D := E.sourceNormalizerModel_at structural
  let π := D.permutation
  let q := π.rangeRestrict
  let hTV := ((structural L S.hypothesis).2.2 V S.chosen).1
  let : IsElementaryAbelian 2 V := S.chosen.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf V.le_normalizer
  let : W.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hk : q.ker = centralizer (W : Set N) := π.ker_rangeRestrict.trans (normalizerModel_kernel D)
  let ρ := NormalElementaryQuotient.representation W q π.rangeRestrict_surjective hk
  let σ := BinaryPermutation.naturalRepresentation (Fin 7)
  let e : W ≃* Multiplicative (BinaryPermutation.natural (Fin 7)) :=
    (subgroupOfEquivOfLe V.le_normalizer).trans
      (E.coordinates.trans evenWordsEquivNatural.toAddEquiv.toMultiplicative)
  let ea : Additive W ≃+ BinaryPermutation.natural (Fin 7) :=
    AddEquiv.toMultiplicative.symm e
  let F : Additive W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7) :=
    ea.toLinearEquiv (fun c x => ZMod.map_smul ea.toAddMonoidHom c x)
  have hF : ∀ g w, F (ρ g w) = σ (g : Equiv.Perm (Fin 7)) (F w) := by
    intro g w
    obtain ⟨n,rfl⟩ := π.rangeRestrict_surjective g
    have hc := NormalElementaryQuotient.representation_apply W q π.rangeRestrict_surjective hk n w
    have he := D.equivariant n ⟨(w.toMul.val : G),w.toMul.property⟩
    have hh : (⟨((ρ (q n) w).toMul.val : G), (ρ (q n) w).toMul.property⟩ : V) =
        V.normalizerMonoidHom n ⟨(w.toMul.val : G),w.toMul.property⟩ :=
      Subtype.ext (congrArg (fun x : N => (x : G)) hc)
    change evenWordsEquivNatural
      (E.coordinates ⟨((ρ (q n) w).toMul.val : G), (ρ (q n) w).toMul.property⟩).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 7) (π n)
        (evenWordsEquivNatural (E.coordinates ⟨(w.toMul.val : G),w.toMul.property⟩).toAdd)
    rw [← evenWordsEquivNatural_equivariant,hh]
    exact congrArg evenWordsEquivNatural he
  have hA' : A.subgroupOf N ∈ elementaryAbelianMaxSubgroups ((T : Subgroup G).subgroupOf N) := by
    apply (maxFamily_map_injective_iff N.subtype N.subtype_injective _ _).mp
    rwa [map_subgroupOf_eq_of_le hTV, map_subgroupOf_eq_of_le (hA.1.trans hTV)]
  have hmap : ((A.subgroupOf N).map q).map π.range.subtype = (A.subgroupOf N).map π := by
    rw [map_map]
    rfl
  have hn : (A.subgroupOf N).map q ≠ ⊥ := by
    intro hz
    apply hne
    rw [← hmap,hz,Subgroup.map_bot]
  have hb := NormalElementaryQuotient.maxElementary_isBestOffender W q
    π.rangeRestrict_surjective hk ((T : Subgroup G).subgroupOf N) (A.subgroupOf N)
    (fun _ hw => S.chosen.le_sylow hw) hA' hn
  have hm := hb.map_of_fixedCodim ρ σ π.range.subtype π.range.subtype_injective
    (fixedCodim_map_equivariant ρ σ π.range.subtype F hF)
  rwa [hmap] at hm

theorem permutation_surjective_of_thompson_generation_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hgen : L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    Function.Surjective (E.sourceNormalizerModel_at structural).permutation := by
  classical
  let D := E.sourceNormalizerModel_at structural
  let N := normalizer (V : Set G)
  have hTV := ((structural L S.hypothesis).2.2 V S.chosen).1
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      ¬ A ≤ centralizer (V : Set G) := by
    by_contra! hn
    exact E.thompson_not_centralizes_of_generation hgen (sSup_le hn)
  obtain ⟨A,hA,hne⟩ := hex
  have hn : (A.subgroupOf N).map D.permutation ≠ ⊥ := by
    intro hz
    have ha := (Subgroup.map_eq_bot_iff _).mp hz
    rw [normalizerModel_kernel D] at ha
    apply hne
    intro a ha'
    have hh := ha (show (⟨a,hTV (hA.1 ha')⟩ : N) ∈ A.subgroupOf N from ha')
    intro v hv
    exact congrArg Subtype.val (hh ⟨v,V.le_normalizer hv⟩ hv)
  have halt : alternatingGroup (Fin 7) ≤ D.permutation.range := by
    intro a ha
    obtain ⟨l,hl⟩ := S.projection_surjective ⟨a,ha⟩
    refine ⟨⟨l,S.chosen.normalizes l.property⟩,?_⟩
    exact (E.sourceNormalizerModel_component_at structural l).trans (congrArg Subtype.val hl)
  apply MonoidHom.range_eq_top.mp
  exact overgroup_eq_symmetric_of_natural_bestOffender D.permutation.range _ halt
    (map_le_range _ _) (E.maxElementary_image_bestOffender_at structural A hA hn)

theorem thompson_and_symmetric_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      BinarySevenCode.weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      Function.Surjective (E.sourceNormalizerModel_at structural).permutation := by
  have hg := E.thompson_generation_of_weight_six_at structural escape hsix
  exact ⟨hg,E.permutation_surjective_of_thompson_generation_at structural hg⟩

end Setup.NaturalCoordinates

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

