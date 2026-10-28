module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizerStructure
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCenterProfile
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightHalfActor

/-!
# The full adjacent-core intersection of the original seven-centralizer

The actual seven-centralizer in the eight-field core is extraspecial of order
 eight. It contains the original binary center plane, which is self-centralizing
inside that group. The full adjacent two-core centralizes this plane. Its
intersection with the seven-centralizer is therefore exactly the plane.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreIntersection
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction Noncommuting NoncommutingProfile CommutingOneProfile

private theorem extraspecial_eight_four_centralizer
    {G : Type*} [Group G] [Finite G]
    (E Z : Subgroup G) [IsExtraspecial 2 E] [IsMulCommutative Z]
    (hE : Nat.card E = 8) (hZ : Nat.card Z = 4) (hZE : Z ≤ E) :
    E ⊓ centralizer (Z : Set G) = Z := by
  let C := E ⊓ centralizer (Z : Set G)
  have hZC : Z ≤ C := le_inf hZE Z.le_centralizer
  have hCZ : C ≠ E := by
    intro he
    have hcen : Z ≤ centerIn E := by
      intro z hz
      refine ⟨hZE hz,?_⟩
      intro x hx
      have hxC : x ∈ C := he.symm ▸ hx
      exact (hxC.2 z hz).symm
    have hc := card_le_of_le hcen
    rw [hZ,centerIn_eq_map_center,card_map_of_injective E.subtype_injective,
      IsExtraspecial.center_order_p 2 E] at hc
    omega
  have hlt : Nat.card C < 8 := by
    have hle : Nat.card C ≤ Nat.card E := card_le_of_le inf_le_left
    have hne : Nat.card C ≠ Nat.card E := by
      intro he
      exact hCZ (eq_of_le_of_card_ge inf_le_left he.ge)
    omega
  have hd : Nat.card C ∣ 8 := by
    have hd := (C.subgroupOf E).card_subgroup_dvd_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C≤E from inf_le_left)).toEquiv,
      hE] at hd
    exact hd
  have hlo := card_le_of_le hZC
  rw [hZ] at hlo
  have hc : Nat.card C = 4 := by
    interval_cases hn : Nat.card C <;> norm_num [hn] at hd
    all_goals rfl
  exact (eq_of_le_of_card_ge hZC (by omega)).symm

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ

set_option maxHeartbeats 800000 in
/-- In the original mixed pair, the full binary core intersects the
seven-fixed part of the adjacent eight-field core in its binary center plane. -/
theorem source_seven_first_core_intersection
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
    let A := (cartan c).map (bOne_tree_map h)
    (Q Fₛ (base Fₛ true) ⊓ centralizer (A : Set (G₀ Lₛ Sₛ))) ⊓
      Q Fₛ (base Fₛ false) = Z Fₛ (base Fₛ false) := by
  let h : HypothesisF11 Lₛ Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  obtain ⟨hz,hZN,_⟩ := SourceBinaryCenterProfile.source_binary_center_profile
    hG T hempty hM hu hmany hcard e H hH eR
  let ι := (G₀ Lₛ Sₛ).subtype
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let α := base Fₛ false
  let β := base Fₛ true
  let Z₀ := Z Fₛ α
  let C := (cartan c).map φ
  let C₀ := c.D 0 ⊔ c.D 1
  let E := H.pCoreIn 2 ⊓ centralizer (C₀ : Set G)
  have hCmap : C.map ι = C₀ := by
    rw [Subgroup.map_map]
    exact SourceEightHalfActor.original_cartan_image hG T hempty hM hu hmany hcard e H hH eR c
  have hCH : C₀ ≤ H := by
    have hh := c.joint_le.trans ((reduced_commonBorel_le h).trans
      (commonBorel_le_parabolic (L := Lₛ) (S := Sₛ) 1))
    change C₀ ≤ parabolic (locals T M Mc H) Sₛ 0 at hh
    rwa [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1] at hh
  have hC7 : Nat.card C₀ = 7 := by
    have hh := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
    rw [cartan,card_map_of_injective middleMap_injective,
      Nat.card_congr (subgroupOfEquivOfLe c.joint_le).toEquiv] at hh
    exact hh
  obtain ⟨_,hE,hex⟩ := SourceSevenCentralizerStructure.source_seven_fixed_core_structure
    hG T hempty hM hu hmany hcard e H hH eR C₀ hCH hC7
  let _ : IsExtraspecial 2 E := hex
  let _ : ∀ i, Finite (Fₛ i) := finite_endpoints (reduced_triple h)
  have hCstab : C ≤ stabilizer Fₛ α := by
    have hCF : cartan c ≤ Universal.cosetFamily (reducedAmalgam Lₛ Sₛ) false := by
      apply (cartan_le c).trans
      rw [originalMiddle, ←Universal.overlap_eq (reducedAmalgam Lₛ Sₛ)
        (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))]
      exact inf_le_left
    rintro _ ⟨x,hx,rfl⟩
    have hf : x • base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) false =
        base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) false := by
      have hh := hCF hx
      rw [←Subgroup.CosetGeometry.stabilizer_base
        (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) false] at hh
      exact hh
    change φ x • base Fₛ false = base Fₛ false
    rw [←cov.vertex_base false, ←cov.vertex_smul, hf]
  have hCnZ : C ≤ normalizer (Z₀ : Set (G₀ Lₛ Sₛ)) := hCstab.trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer Fₛ α)).mp (Z_normal Fₛ α))
  have hC₀nZ : C₀ ≤ normalizer (Z₀.map ι : Set G) := by
    rw [←hCmap]
    exact (map_mono hCnZ).trans (Z₀.le_normalizer_map ι)
  have hZcard : Nat.card (Z₀.map ι) = 4 := by
    rw [card_map_of_injective (G₀ Lₛ Sₛ).subtype_injective]
    exact hz
  have hZC : Z₀.map ι ≤ centralizer (C₀ : Set G) :=
    SourceBinaryCenterProfile.seven_centralizes_four C₀ (Z₀.map ι) hC7 hZcard hC₀nZ
  have hab : (graph Fₛ).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hNQ : (ballKernel Fₛ α 2).pCoreIn 2 ≤ Q Fₛ β := by
    rw [←reduced_neighborCoreIntersection_eq_second_core h hab.symm]
    exact neighborCoreIntersection_le Fₛ hab.symm
  have hQmap : (Q Fₛ β).map ι = H.pCoreIn 2 := by
    have hh := reduced_base_Q_map h true
    change (Q Fₛ β).map ι = (parabolic (locals T M Mc H) Sₛ 0).pCoreIn 2 at hh
    rwa [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1] at hh
  have hZβ : Z₀.map ι ≤ H.pCoreIn 2 := hQmap ▸ map_mono (hZN.trans hNQ)
  let _ : IsElementaryAbelian 2 Z₀ := graph_Z_elementary (reduced_triple h) α
  let _ : IsElementaryAbelian 2 (Z₀.map ι) := IsElementaryAbelian.map ι
  have hself : E ⊓ centralizer (Z₀.map ι : Set G) = Z₀.map ι :=
    extraspecial_eight_four_centralizer E (Z₀.map ι) hE hZcard (le_inf hZβ hZC)
  have hαC : (Q Fₛ α).map ι ≤ centralizer (Z₀.map ι : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨z,hz,rfl⟩
    exact congrArg ι (graph_Q_centralizes_Z (reduced_triple h) α hx z hz)
  have hZα : Z₀ ≤ Q Fₛ α :=
    (source_Z_Q_U (reduced_triple h) α).1.trans (map_subtype_le _)
  have hfixed : E ⊓ (Q Fₛ α).map ι = Z₀.map ι := by
    apply le_antisymm
    · exact (inf_le_inf_left E hαC).trans_eq hself
    · exact le_inf (le_inf hZβ hZC) (map_mono hZα)
  apply Subgroup.map_injective (G₀ Lₛ Sₛ).subtype_injective
  change ((Q Fₛ β ⊓ centralizer (C : Set (G₀ Lₛ Sₛ))) ⊓ Q Fₛ α).map ι = Z₀.map ι
  rw [map_inf _ _ _ (G₀ Lₛ Sₛ).subtype_injective,
    ←map_inf_centralizer_of_injective ι (G₀ Lₛ Sₛ).subtype_injective,hQmap,hCmap]
  exact hfixed

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreIntersection
