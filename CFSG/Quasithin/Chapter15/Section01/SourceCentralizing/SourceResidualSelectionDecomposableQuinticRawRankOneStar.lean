module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawRankOneImage
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.SpecificGroups.SL2.EvenCentralKernel
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.GroupTheory.SimpleSubgroupSmallIndex

/-!
# Rank-one exclusions for the original C.2.7 star image

The native even linear-two central-cover theorem makes the actual core-to-star
kernel a two-group. The original core quotient has trivial two-core, so that
map is bijective. Its center is trivial, and the actual seed-normalizer image
is therefore the same rank-one group. The proved original normalizer-image
exclusion now applies to the same L, including the alternating-five row.
No whole-M generation or residual-centralization premise is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original core-to-star map has trivial kernel in every binary
linear-two row. Quasisimplicity excludes degree one internally. -/
theorem raw_linearTwo_coreToStar_bijective {I R N L : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple I R N L)
    (F : BinaryField)
    (e : starImage L R L ≃* SL(2,F.Carrier)) :
    Function.Bijective (coreToStar hi.normalizes) := by
  let : (L.subgroupOf (L ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  let hq : IsQuasisimple (starImage L R L) :=
    (star_fitting_quasisimple (source_join_input hi)).2
  let : IsSimpleGroup ((starImage L R L) ⧸ center (starImage L R L)) := hq.simple
  let : Nontrivial (starImage L R L) :=
    (QuotientGroup.mk'_surjective (center (starImage L R L))).nontrivial
  have hF : 2 ≤ F.degree := by
    by_contra hn
    have hd : F.degree = 1 := by have := F.degree_pos; omega
    have hc : Nat.card (starImage L R L) ≤ 6 := by
      rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two,F.card_eq,hd]
      decide
    exact Group.IsPerfect.not_isSolvable (starImage L R L)
      (Group.isSolvable_of_card_le_six hc)
  let ep := e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL
  let f := ep.toMonoidHom.comp (coreToStar hi.normalizes)
  have hk : f.ker = (coreToStar hi.normalizes).ker :=
    MonoidHom.ker_comp_of_injective _ ep.toMonoidHom ep.injective
  let c : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) PSL(2,F.Carrier) :=
    { f with
      surjective := ep.surjective.comp (coreToStar_surjective hi.normalizes)
      isPerfect := hi.quasisimple.toIsPerfect
      ker_le_center := hk ▸ coreToStar_ker_central_from_source hi }
  have hp := Theory.SL2.perfect_central_kernel_isTwoGroup F.degree hF F.card_eq c
  change IsPGroup 2 f.ker at hp
  have hker : f.ker = ⊥ := by
    apply bot_unique
    rw [←pCore_quotient_pCore_eq_bot 2]
    exact le_sSup ⟨inferInstance,hp⟩
  have hf : Function.Injective f := f.ker_eq_bot_iff.mp hker
  refine ⟨?_,coreToStar_surjective hi.normalizes⟩
  intro x y hxy
  apply hf
  exact congrArg ep hxy

/-- The actual original star image cannot be a binary linear-two group.
The same component and original seed-normalizer action are retained. -/
theorem PreparedChosenModule.raw_component_star_not_rankOne
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (Z1 : Set G)))
    (hlocal : L ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hn : let D := M ⊓ centralizer (Z1 : Set G); let A := (pResidual 2 D).map D.subtype
      A ⊔ ⁅V,A⁆ ≤ normalizer (L : Set G))
    (hmove : let D := M ⊓ centralizer (Z1 : Set G); let A := (pResidual 2 D).map D.subtype
      ⁅L,⁅V,A⁆⁆ ≠ ⊥)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (F : BinaryField) :
    IsEmpty (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ≃*
      SL(2,F.Carrier)) := by
  refine ⟨fun e => ?_⟩
  let ec := (MulEquiv.ofBijective (coreToStar hi.normalizes)
    (raw_linearTwo_coreToStar_bijective hi F e)).trans e
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro x hx
    exact ec.map_eq_one_iff.mp
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot.le
        ((centerCongr ec ⟨x,hx⟩).property))
  obtain ⟨_,f,_,_,_,hfs,hfc,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne ⟨hL.1,hlocal⟩ hq hf hout houtM
  have hfi : Function.Injective f := f.ker_eq_bot_iff.mp
    (bot_unique (hfc.trans hz.le))
  let ei := MulEquiv.ofBijective f ⟨hfi,hfs⟩
  exact (h.raw_component_normalizer_not_rankOne hG T hM hJ hu hZ hZne hSyl hL
    hlocal hq hf hout houtM hcontrol hbound hI hn hmove F.Carrier).false
      (ei.symm.trans ec)

/-- The alternating-five star row is the degree-two instance on the same L. -/
theorem PreparedChosenModule.raw_component_star_not_alternatingFive
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (Z1 : Set G)))
    (hlocal : L ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hn : let D := M ⊓ centralizer (Z1 : Set G); let A := (pResidual 2 D).map D.subtype
      A ⊔ ⁅V,A⁆ ≤ normalizer (L : Set G))
    (hmove : let D := M ⊓ centralizer (Z1 : Set G); let A := (pResidual 2 D).map D.subtype
      ⁅L,⁅V,A⁆⁆ ≠ ⊥)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L) :
    IsEmpty (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ≃*
      alternatingGroup (Fin 5)) := by
  refine ⟨fun e => ?_⟩
  let ea : alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := BinaryField.four.Carrier) (by
        change Nat.card (GaloisField 2 2) = 4
        rw [GaloisField.card 2 2 (by decide)]
        decide)).some.symm.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  exact (h.raw_component_star_not_rankOne hG T hM hJ hu hZ hZne hSyl hL hlocal
    hq hf hout houtM hcontrol hbound hI hn hmove hi BinaryField.four).false
      (e.trans ea)

end CFSG.Quasithin.Chapter15.Section01
