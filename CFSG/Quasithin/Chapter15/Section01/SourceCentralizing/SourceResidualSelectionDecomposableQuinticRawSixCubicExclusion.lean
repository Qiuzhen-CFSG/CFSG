module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicLocal
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicNaturality
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCentralResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawParabolicPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixNormalizer

/-!
# Excluding the actual cubic-center A₆ row

The original seed action normalizes both canonical source parabolics.
Source placement puts each into one of the two original intersections.
The actual cubic residual puts the first intersection in Mc as well.
Their proved generation then contradicts the selected L lying outside Mc.
The proof retains the full cubic center and original C.2.7 input; it uses
no whole-core reconstruction, whole-M generation or residual prior.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original same-L central A₆ row with cubic core center is impossible. -/
theorem PreparedChosenModule.raw_not_cubic_six_core
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
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G))
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) : False := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let N := centralizer (Z1 : Set G) ⊓ Mc
  obtain ⟨hn,P,Q,hPL,hQL,_,_,hgen,hfitP,hfitQ,⟨eP⟩,⟨eQ⟩,hnoP,hnoQ,hpair⟩ :=
    h.raw_six_cubic_source_pair hG T hM.1.2 hZ hZne hL hi.quasisimple hi.fitting e hc
  have hnorm : S ≤ normalizer (P : Set G) ∧ S ≤ normalizer (Q : Set G) := by
    have hh := h.raw_six_cubic_sylow_natural hG T hM hJ hu hZ hZne hL houtM hi e hc hn
    exact ⟨fun x hx => (hpair ⟨x,hx⟩ (hh ⟨x,hx⟩)).1,
      fun x hx => (hpair ⟨x,hx⟩ (hh ⟨x,hx⟩)).2⟩
  have htwo : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  have hleft := h.raw_parabolic_placement_of_sylow_normalizes hG T hM hJ hu hZ hZne
    hSyl hL.1 hPL hnorm.1 hfitP
    (Or.inl (NormalSymmetricThreeExtension.normalized_join P S hnorm.1 eP htwo)) hnoP
  have hright := h.raw_parabolic_placement_of_sylow_normalizes hG T hM hJ hu hZ hZne
    hSyl hL.1 hQL hnorm.2 hfitQ
    (Or.inl (NormalSymmetricThreeExtension.normalized_join Q S hnorm.2 eQ htwo)) hnoQ
  have hML := h.raw_six_central_intersection_le_partner hG T hM.1.2 hu hfull hZ hZne
    hL.1 hi.quasisimple (ComponentModels.source20_sylow_intersection hL.2) hcubic e
  have hMLN : M ⊓ L ≤ N := le_inf (inf_le_right.trans hL.1) hML
  apply hi.outside
  calc
    L = P ⊔ Q := hgen.symm
    _ ≤ N := sup_le
      (hleft.elim (fun hh => hh.trans hMLN) (fun hh => hh.trans inf_le_left))
      (hright.elim (fun hh => hh.trans hMLN) (fun hh => hh.trans inf_le_left))

/-- Both ordinary and cubic core-center possibilities are excluded for
the actual same-L C.2.7 six-letter star row. -/
theorem PreparedChosenModule.raw_not_six_star_image
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
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G))
    (e : (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ⧸
      center (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L)) ≃*
        alternatingGroup (Fin 6)) : False := by
  have hc := h.raw_six_star_core_center_three hG T hM hJ hu hfull hZ hZne
    hSyl hL houtM hi hcubic e
  let cs : PerfectCentralCovering.Cover (L ⧸ pCore 2 L)
      (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L) :=
    ⟨coreToStar hi.normalizes,coreToStar_surjective hi.normalizes,
      hi.quasisimple.toIsPerfect,coreToStar_ker_central_from_source hi⟩
  exact h.raw_not_cubic_six_core hG T hM hJ hu hfull hZ hZne hSyl hL houtM hi
    hcubic (cs.quotientCenterEquiv.trans e) hc

/-- The actual normalizer-image central-six row is impossible as well;
the two images are compared only through their full central covers. -/
theorem PreparedChosenModule.raw_not_six_normalizer_image
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
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G)) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    (I ⧸ center I) ≃* alternatingGroup (Fin 6) → False := by
  dsimp only
  intro e
  obtain ⟨a⟩ := h.raw_normalizer_star_central_quotients hG T hM hJ hu hZ hZne hL houtM hi
  exact h.raw_not_six_star_image hG T hM hJ hu hfull hZ hZne hSyl hL houtM hi
    hcubic (a.symm.trans e)

end CFSG.Quasithin.Chapter15.Section01
