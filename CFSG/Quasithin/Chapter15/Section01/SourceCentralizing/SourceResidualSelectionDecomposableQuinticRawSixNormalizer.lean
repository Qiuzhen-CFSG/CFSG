module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerQuotient
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixNatural

/-! The original core maps centrally onto both the actual normalizer image
and the C.2.7 star. These full covers identify their central quotients,
without identifying the images or their centers. Thus an actual normalizer
A6 central quotient supplies the same original SmallMSPair reconstruction:
a whole natural six-block or the literal cubic center of L/O2(L).
The only Sylow hypothesis is the original marked Sylow in C_G(Z1).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The two actual central covers have isomorphic central quotients.
Their full kernels are retained; no equality of images or centers is asserted. -/
theorem PreparedChosenModule.raw_normalizer_star_central_quotients
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    Nonempty ((I ⧸ center I) ≃*
      (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ⧸
        center (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L))) := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let H := L ⊔ (S ⊓ normalizer (L : Set G))
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
  obtain ⟨_,f,_,_,_,hf,hk,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside houtM
  let cN : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) I :=
    ⟨f,hf,hi.quasisimple.toIsPerfect,hk⟩
  let cS : PerfectCentralCovering.Cover (L ⧸ pCore 2 L)
      (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L) :=
    ⟨coreToStar hi.normalizes,coreToStar_surjective hi.normalizes,
      hi.quasisimple.toIsPerfect,coreToStar_ker_central_from_source hi⟩
  exact ⟨cN.quotientCenterEquiv.symm.trans cS.quotientCenterEquiv⟩

/-- An A6 central quotient of the actual normalizer image reconstructs a
whole natural six-block on the same L, or retains its full cubic core center.
The original Q1 is never assumed to be Sylow in its join with L. -/
theorem PreparedChosenModule.raw_six_normalizer_block_or_cubic_core_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    (I ⧸ center I) ≃* alternatingGroup (Fin 6) →
      IsAlternatingBlock L 6 ∨ Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  dsimp only
  intro e
  obtain ⟨a⟩ := h.raw_normalizer_star_central_quotients hG T hM hJ hu hZ hZne hL houtM hi
  exact raw_six_block_or_cubic_core_center T hu hs hi (a.symm.trans e)

end CFSG.Quasithin.Chapter15.Section01
