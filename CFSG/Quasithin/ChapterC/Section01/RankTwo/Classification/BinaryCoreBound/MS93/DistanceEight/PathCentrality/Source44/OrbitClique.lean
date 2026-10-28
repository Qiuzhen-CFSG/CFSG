module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OrbitClique.Action
public import Theory.ElementaryAbelian.AdjacentSubgroupClique

/-!
# Binary escaping-seed displacement transfer

The conjugate seeds form an adjacent-subgroup clique. Either two escaping
seeds already span the full module, or the orbit intersection has index two
in the seed. In the latter case the existing seven-point star calculation
fixes the seed pointwise under its marked point stabilizer. Both cases
transfer the displacement bound from the escaping span to the whole module.

This proves the binary orbit implication needed from
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(1.6), printed pp.845--847, on the actual faithful marked action.
-/

public section
open Subgroup Matrix
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
namespace OrbitClique
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

 theorem escaping_orbit_cases (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ) :
    actionEscapingSpan ρ (markedPointStabilizer d.marking d.point) d.involution d.seed=⊤ ∨
      (actionOrbitCore ρ d.seed).relIndex d.seed=2 := by
  obtain ⟨e,he⟩ := Star.exists_point_marking d.marking d.point d.point_ne_zero
  obtain ⟨n,hn⟩ := involution_conjugator ρ d e
  let K := markedPointStabilizer d.marking d.point
  let X := actionEscapingSpan ρ K d.involution d.seed
  let W := actionConjugate ρ d.seed
  have hescape : d.involution∉NormalizerTransfer.rightConjugate K n := by
    rw [mem_rightConjugate_iff,hn]
    exact fun hh => PSL3Two.PointDoubleCoset.swap_not_mem ((he _).mpr hh)
  have hescape' : d.involution∉NormalizerTransfer.rightConjugate K (n*d.involution⁻¹) := by
    rw [mem_rightConjugate_iff]
    have hconj : (n*d.involution⁻¹)*d.involution*(n*d.involution⁻¹)⁻¹=
        n*d.involution*n⁻¹ := by group
    rw [hconj,hn]
    exact fun hh => PSL3Two.PointDoubleCoset.swap_not_mem ((he _).mpr hh)
  have hWX : W n≤X := le_iSup_of_le n (le_iSup_of_le hescape le_rfl)
  have hWX' : W (n*d.involution⁻¹)≤X :=
    le_iSup_of_le (n*d.involution⁻¹) (le_iSup_of_le hescape' le_rfl)
  by_cases hseed : d.seed=⊤
  · left
    apply top_unique
    intro x _
    obtain ⟨y,rfl⟩ := (ρ n⁻¹).surjective x
    exact hWX ⟨y,hseed ▸ mem_top _,rfl⟩
  have hne : W n≠W (n*d.involution⁻¹) := by
    intro hh
    apply swap_moves_seed ρ d hseed e he
    calc
      actionConjugate ρ d.seed (e PSL3Two.PointDoubleCoset.swap) =
          (W (n*d.involution⁻¹)).map (ρ n).toMonoidHom := by
        rw [← map_reflected_pair ρ d e n hn,conjugate_map]
      _ = (W n).map (ρ n).toMonoidHom := congrArg (fun U:Subgroup E=>U.map (ρ n).toMonoidHom) hh.symm
      _ = d.seed := conjugate_cancel ρ d.seed n
  have hcard (g : SL) : Nat.card (W g)=Nat.card (W n) := by
    change Nat.card (d.seed.map (ρ g⁻¹).toMonoidHom)=Nat.card (d.seed.map (ρ n⁻¹).toMonoidHom)
    rw [card_map_of_injective (ρ g⁻¹).injective,card_map_of_injective (ρ n⁻¹).injective]
  rcases Subgroup.binary_clique_core_or_span W n (n*d.involution⁻¹) hne hcard
    (all_pair_indices_le_two ρ d) with hc | ht
  · right
    change (actionOrbitCore ρ d.seed).relIndex (actionConjugate ρ d.seed n)=2 at hc
    rwa [orbitCore_relIndex_conjugate] at hc
  · left
    apply top_unique
    rw [← d.generates]
    change (⨆ g,W g)≤X
    rw [ht]
    exact sup_le hWX hWX'

 theorem displacement_transfer (ρ : SL →* MulAut E) (hf : Function.Injective ρ)
    (d : EscapingConfiguration ρ) :
    actionDisplacement ρ (zpowers d.involution) ⊤ ≤
      actionDisplacement ρ (zpowers d.involution)
        (actionEscapingSpan ρ (markedPointStabilizer d.marking d.point) d.involution d.seed) := by
  rcases escaping_orbit_cases ρ d with hwhole | hline
  · rw [hwhole]
  · exact displacement_transfer_of_orbitCore_index_two ρ hf d hline
end OrbitClique
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
