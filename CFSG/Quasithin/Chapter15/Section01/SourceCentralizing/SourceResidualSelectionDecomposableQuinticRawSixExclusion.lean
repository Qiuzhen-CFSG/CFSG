module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixParabolics
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixNatural

/-! The ordinary A6 block is impossible for the actual original component:
its two intersections generate L, while both lie in the marked partner.
The original C.2.7 six-letter star row consequently retains precisely its
cubic core-quotient center. No core/star/normalizer equality is assumed. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original residual identity excludes the whole ordinary A6 block
on the same selected local component. -/
theorem PreparedChosenModule.raw_not_ordinary_six_block
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
    (hb : IsAlternatingBlock L 6) : False := by
  have hgen := h.raw_six_original_intersections_generate hG T hM hJ hu hZ hZne
    hSyl hL houtM hi hb
  obtain ⟨ρ,⟨m⟩,_⟩ := hb.2.2
  have hsub := h.raw_six_intersection_le_partner T hM.1.2 hu hfull
    (ComponentModels.source20_sylow_intersection hL.2) hcubic m.quotientIso
  apply hi.outside
  rw [←hgen]
  exact sup_le (le_inf (inf_le_right.trans hL.1) hsub) inf_le_left

/-- In the actual C.2.7 six-letter star row, the full core-quotient center
has order three; the natural block alternative is genuinely eliminated. -/
theorem PreparedChosenModule.raw_six_star_core_center_three
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
        alternatingGroup (Fin 6)) :
    Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  rcases raw_six_block_or_cubic_core_center T hu hSyl hi e with hb | hc
  · exact (h.raw_not_ordinary_six_block hG T hM hJ hu hfull hZ hZne hSyl hL houtM hi hcubic hb).elim
  · exact hc

end CFSG.Quasithin.Chapter15.Section01
