module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPath
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootTrappedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth

/-!
# Full neighboring seed budgets without radius fixedness

Transport the internally constructed root critical path to the original
vertex. This bounds every full neighboring seed by q cubed over its actual
edge seed, including all central attachments. Consequently a normalized
full kernel join lies in the original B-preimage. Its full seed index is
bounded by the same directed kernel index, and the same stabilizer selector
transports that bound to the original seed.

Source: the small normalized join in MS93 (5.12)(2), pp.925--926.
No fixed-radius premise or root-image premise on the original backward path
is used. The normalization remains an explicit local input to this helper.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every full neighboring seed satisfies the cube bound at b=4. The
root critical path needed for the estimate is constructed internally. -/
theorem Input.replacement_distance_four_neighbor_seed_index_le_cube
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {u v s : Vertex d.radical} (hu : color d.radical u=false)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s) :
    (Z d.radical s).relIndex (Z d.radical v) ≤ Nat.card F^3 := by
  obtain ⟨c,e,path,_,hi⟩ := h.replacement_distance_four_exists_root_critical_path d geometry hb
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical path.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical hu
  let y := g⁻¹*j
  have hy : act d.radical y c=u := by
    rw [hg,act_mVertex]
    dsimp only [y]
    rw [mul_inv_cancel_left,←hj]
  have hs : (Q d.radical (act d.radical y c)).relIndex
      (Z d.radical (act d.radical y e)) < Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective,hi]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  exact h.replacement_root_neighbor_seed_index_le_cube d (path.act y)
    (by omega) (by rw [hy]; exact hus) hvs hs

/-- Normalization of the full original kernel join bounds its full seed
index by the same directed Q-index, without fixed-radius assumptions. -/
theorem Input.replacement_distance_four_normalized_neighbor_kernel_budget
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {u v a s : Vertex d.radical} (hu : color d.radical u=false)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (hn : Ltilde d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    (Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u ≤
        B d.radical u (geometry.Z_normal u) ∧
      (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical v) ≤
        (Q d.radical a).relIndex (Z d.radical v) := by
  let Y := (Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u
  have hb2 : 2 < geometry.b d.radical := by omega
  have hSV : Z d.radical v ⊔ Z d.radical u ≤ V d.radical u :=
    neighbor_seed_join_le_radius hus hvs
  let := finite_stabilizer d.radical u
  let : Finite (Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hSV.trans
      ((geometry.V_le_Q hb2 u hu).trans (fun _ hx => hx.1))))
      (inclusion_injective _)
  have hbound := h.replacement_distance_four_neighbor_seed_index_le_cube d geometry hb hu hus hvs
  have hiY : (Z d.radical u).relIndex Y ≤ Nat.card F^3 :=
    (relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
      ((neighbor_seed_join_index_le geometry (by omega) hu hus hvs).trans hbound)
  have hYB := h.replacement_small_radius_le_B d geometry hb2 hu Y
    ((sup_le_sup inf_le_left le_rfl).trans hSV) hn
    (hiY.trans_lt (Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide : 3<4)))
  have hWB : Z d.radical v ⊓ Q d.radical a ≤ B d.radical u (geometry.Z_normal u) :=
    le_sup_left.trans hYB
  let := finite_Z d.radical v
  have hi := relIndex_le_of_le_left hWB (L := Z d.radical v) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hi
  exact ⟨hYB,hi⟩

/-- The retained stabilizer selector transfers the full seed bound to its
original seed. No saturation of a central attachment is assumed. -/
theorem Input.replacement_distance_four_normalized_selected_seed_budget
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {u v a s : Vertex d.radical} (hu : color d.radical u=false)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hn : Ltilde d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a) ≤
      (Q d.radical a).relIndex (Z d.radical v) := by
  have hi := (h.replacement_distance_four_normalized_neighbor_kernel_budget d
    geometry hb hu hus hvs hn).2
  have hB : (B d.radical u (geometry.Z_normal u)).map (MulAut.conj y⁻¹).toMonoidHom =
      B d.radical u (geometry.Z_normal u) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := geometry) (by omega) u hu
        ((stabilizer d.radical u).inv_mem hy))
  have htransport : (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical v) =
      (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a) := by
    rw [←hya,Z_act]
    conv_lhs => rw [←hB]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective
  exact htransport.symm.trans_le hi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
