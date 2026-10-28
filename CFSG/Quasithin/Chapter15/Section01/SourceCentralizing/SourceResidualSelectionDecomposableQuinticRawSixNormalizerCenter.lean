module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixNormalizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixExclusion

/-! The original ordinary-six exclusion removes the natural-block branch
of the actual normalizer reconstruction. What remains is the literal
center of order three in L/O2(L), with both central comparison kernels
retained and no equality between normalizer and star images. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- An A6 central quotient of the original normalizer image forces a
cubic center in the full original two-core quotient. -/
theorem PreparedChosenModule.raw_six_normalizer_core_center_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤ centralizer (V : Set G)) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    (I ⧸ center I) ≃* alternatingGroup (Fin 6) → Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  dsimp only
  intro e
  rcases h.raw_six_normalizer_block_or_cubic_core_center hG T hM hJ hu hZ hZne hL hSyl houtM hi e with hb | hc
  · exact (h.raw_not_ordinary_six_block hG T hM hJ hu hfull hZ hZne hSyl hL houtM hi hcubic hb).elim
  · exact hc

end CFSG.Quasithin.Chapter15.Section01
