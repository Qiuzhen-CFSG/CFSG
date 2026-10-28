module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinCoverage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.BaumannLift
public import Theory.SpecificGroups.SL2.PairSylowNormalizer

/-!
# The actual paired Borel and its placement in N(V)

Take the normalizer of the genuine Sylow intersection in the component
pair, then its full inverse image under the literal plus map. The two-group
kernel lies in the original Sylow subgroup. Baumann heredity therefore
lifts normalizing its plus image to normalizing Baum(Tᵥ), and the source
normalizer control places this Borel in N(V). The two rank-one tori give
an odd-square divisor of its order.

Source: Aschbacher--Smith 13.6.14, printed pp.929--930.
-/

public section
open Subgroup Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
variable {G : Type*} [Group G] [Finite G]

/-- Construct the source Borel from the actual paired natural Baumann image. -/
theorem exists_pairBorel_source
    (K L T V : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : IsPGroup 2 (joinPlusMap K L T z v hL hz).ker)
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (P : Sylow 2 ↥(K ⊔ Tv T v))
    (hP : (P : Subgroup ↥(K ⊔ Tv T v)).map (K ⊔ Tv T v).subtype = Tv T v)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz (Kminus K T v) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (hB : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
      plusImage K L T z v hL hz (Tv T v) ⊓ plusImage K L T z v hL hz (Kminus K T v))
    (hc : Gv v ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G) ≤ normalizer (V : Set G)) :
    ∃ B : Subgroup G, B ≤ normalizer (V : Set G) ∧
      B ≤ K ⊔ Tv T v ∧
      plusImage K L T z v hL hz B ≤ plusImage K L T z v hL hz (Kminus K T v) ∧
      (Nat.card F - 1) ^ 2 ∣ Nat.card B := by
  let A := K ⊔ Tv T v
  change (P : Subgroup A).map A.subtype = Tv T v at hP
  let q := joinPlusMap K L T z v hL hz
  have hq := joinPlusMap_surjective_of_plus_placement_source K L T z v hL hz hLv
  let C := plusImage K L T z v hL hz (Kminus K T v)
  let := plusImage_Kminus_normal_source K L T z v hL hz hK
  let Q := P.mapSurjective (f := q) hq
  obtain ⟨R,hR⟩ := Q.exists_sylow_map_eq_inf_of_normal C
  let N := normalizer ((R : Subgroup C) : Set C)
  let D := N.map C.subtype
  let B := (D.comap q).map A.subtype
  have hPinternal : (P : Subgroup A) = (Tv T v).subgroupOf A := by
    exact (comap_map_eq_self_of_injective A.subtype_injective (P : Subgroup A)).symm.trans
      (congrArg (Subgroup.comap A.subtype) hP)
  have hQ : (Q : Subgroup _) = plusImage K L T z v hL hz (Tv T v) := by
    change (P : Subgroup A).map q = _
    rw [hPinternal]
    exact joinPlusMap_image_source K L T z v hL hz _ le_sup_right
  have hNR : D ≤ normalizer (plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) : Set _) := by
    rw [hB,←hQ,←hR]
    exact (R : Subgroup C).le_normalizer_map C.subtype
  have hBi : (ChapterB.baumann (Tv T v)).subgroupOf A = ChapterB.baumann (P : Subgroup A) := by
    have hm : (ChapterB.baumann (P : Subgroup A)).map A.subtype = ChapterB.baumann (Tv T v) := by
      simpa only [ChapterB.baumann,ChapterB.thompsonAlpha,hP] using baumann_map_injective A.subtype A.subtype_injective (P : Subgroup A)
    rw [←hm]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hBmap : (ChapterB.baumann (P : Subgroup A)).map q =
      plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) := by
    rw [←hBi]
    exact joinPlusMap_image_source K L T z v hL hz (ChapterB.baumann (Tv T v)) (inf_le_left.trans le_sup_right)
  have hBN : B ≤ normalizer (V : Set G) := by
    rintro b ⟨a,ha,rfl⟩
    apply hc
    refine ⟨(sup_le hK.1.1 inf_le_right) a.property,?_⟩
    have hn : a ∈ normalizer (ChapterB.baumann (P : Subgroup A) : Set A) := by
      rw [←baumann_normalizer_comap_of_two_kernel q P hk,hBmap]
      exact hNR ha
    have hm := (ChapterB.baumann (P : Subgroup A)).le_normalizer_map A.subtype
      (mem_map_of_mem A.subtype hn)
    rwa [←hBi,map_subgroupOf_eq_of_le (show ChapterB.baumann (Tv T v) ≤ A from
      inf_le_left.trans (show Tv T v ≤ A from le_sup_right))] at hm
  have hBA : B ≤ A := map_subtype_le _
  have hplusB : plusImage K L T z v hL hz B = D := by
    rw [←joinPlusMap_image_source K L T z v hL hz B hBA]
    change (((D.comap q).map A.subtype).comap A.subtype).map q = D
    rw [comap_map_eq_self_of_injective A.subtype_injective,
      map_comap_eq_self_of_surjective hq]
  have hcardN : (Nat.card F - 1) ^ 2 ∣ Nat.card N := by
    let D₂ := Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F
    let S : Sylow 2 D₂ := R.mapSurjective (f := e.toMonoidHom) e.surjective
    have he : N.map e.toMonoidHom = normalizer ((S : Subgroup D₂) : Set D₂) := by
      change (normalizer ((R : Subgroup C) : Set C)).map e.toMonoidHom =
        normalizer (((R : Subgroup C).map e.toMonoidHom : Subgroup D₂) : Set D₂)
      exact map_normalizer_eq_of_bijective (R : Subgroup C) e.bijective
    rw [Nat.card_congr (equivMapOfInjective N e.toMonoidHom e.injective).toEquiv,
      he]
    exact Matrix.SpecialLinearGroup.odd_square_dvd_card_pair_sylow_normalizer S
  have hcardD : Nat.card D ∣ Nat.card B := by
    have hh := (D.comap q).card_map_dvd q
    rw [map_comap_eq_self_of_surjective hq] at hh
    exact (Nat.card_congr (equivMapOfInjective (D.comap q) A.subtype A.subtype_injective).toEquiv) ▸ hh
  refine ⟨B,hBN,hBA,?_,?_⟩
  · rw [hplusB]
    exact map_subtype_le _
  · have hND : Nat.card N = Nat.card D :=
      Nat.card_congr (equivMapOfInjective N C.subtype C.subtype_injective).toEquiv
    exact (hND ▸ hcardN).trans hcardD

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
