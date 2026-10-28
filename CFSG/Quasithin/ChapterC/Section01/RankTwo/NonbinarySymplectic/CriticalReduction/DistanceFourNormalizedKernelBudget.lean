module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedIndices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootTrappedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanResidual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexPathSelection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# The full seed budget from the retained far critical kernel

Let the actual far selector send a to v while fixing u. If the residual at
u normalizes (Z_v intersect Q_a) joined with Z_u, the cube bound puts this
entire join in the original B_u. The far critical path gives the full
Z_v-intersection index q. Transport along that same selector therefore
bounds the full original Z_a-index, and hence its U_a-index, by q.

With the actual midpoint equality, this also bounds the image modulo Q_a
of the original full residual [Q_u,L_u]. No replacement of that residual
by a span commutator, or saturation assumption, enters either conclusion.
Source: MS93 (5.12)(3), printed p.927, followed by (3.10)(i), p.880.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem full_seed_B_index_act {M : Type*} [Group M] [Finite M]
    {R : Subgroup M} (geometry : Geometry R) (hb : 2 < geometry.b R)
    {u a : Vertex R} (hu : color R u=false)
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R u) :
    (B R u (geometry.Z_normal u)).relIndex (Z R (act R y a)) =
      (B R u (geometry.Z_normal u)).relIndex (Z R a) := by
  have hB : (B R u (geometry.Z_normal u)).map (MulAut.conj y⁻¹).toMonoidHom =
      B R u (geometry.Z_normal u) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := geometry) hb u hu
        ((stabilizer R u).inv_mem hy))
  rw [Z_act]
  conv_lhs => rw [←hB]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Normality of the actual full far-kernel join gives both the far and
the original full seed budgets along the unchanged residual selector. -/
theorem Input.replacement_distance_four_normalized_full_kernel_seed_budget
    {geometry : Geometry d.radical} {a e u v s : Vertex d.radical}
    (back : CriticalPath d.radical geometry u e) (hb : geometry.b d.radical=4)
    (ha : color d.radical a=false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (next : CriticalPath d.radical geometry v a)
    (hn : Ltilde d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    (Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u ≤
        B d.radical u (geometry.Z_normal u) ∧
      (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical v) ≤ Nat.card F ∧
      (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a) ≤ Nat.card F ∧
      (B d.radical u (geometry.Z_normal u)).relIndex (U d.radical a) ≤ Nat.card F := by
  let Y := (Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u
  have hb2 : 2 < geometry.b d.radical := by omega
  have hroot := (h.replacement_distance_four_fixed_critical_indices d hb ha hfixed back).2
  have hsmall : (Q d.radical u).relIndex (Z d.radical e) < Nat.card F^2 := by
    rw [hroot]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hSV : Z d.radical v ⊔ Z d.radical u ≤ V d.radical u :=
    neighbor_seed_join_le_radius hus hvs
  let := finite_stabilizer d.radical u
  let : Finite (Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hSV.trans
      ((geometry.V_le_Q hb2 u back.start_color).trans (fun _ hx => hx.1))))
      (inclusion_injective _)
  have hbound := h.replacement_root_neighbor_seed_index_le_cube d back (by omega) hus hvs hsmall
  have hiY : (Z d.radical u).relIndex Y ≤ Nat.card F^3 :=
    (relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
      ((neighbor_seed_join_index_le geometry (by omega) back.start_color hus hvs).trans hbound)
  have hYB := h.replacement_small_radius_le_B d geometry hb2 back.start_color Y
    ((sup_le_sup inf_le_left le_rfl).trans hSV) hn
    (hiY.trans_lt (Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide : 3<4)))
  have hWB : Z d.radical v ⊓ Q d.radical a ≤ B d.radical u (geometry.Z_normal u) :=
    le_sup_left.trans hYB
  let := finite_Z d.radical v
  have hvZ := relIndex_le_of_le_left hWB (L := Z d.radical v) index_ne_zero_of_finite
  rw [inf_relIndex_left,
    (h.replacement_distance_four_fixed_critical_indices d hb ha hfixed next).1] at hvZ
  have htransport : (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical v) =
      (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a) := by
    rw [←hya]
    exact full_seed_B_index_act geometry hb2 back.start_color y hy
  have haZ := htransport.symm.trans_le hvZ
  let := finite_Z d.radical a
  exact ⟨hYB,hvZ,haZ,
    ((B d.radical u (geometry.Z_normal u)).relIndex_le_of_le_right
      (U_le_Z a) index_ne_zero_of_finite).trans haZ⟩

/-- The same retained kernel normalization and actual midpoint bound the
image of the full original residual, without a span-residual identity. -/
theorem Input.replacement_distance_four_normalized_full_kernel_residual_image
    {geometry : Geometry d.radical} {a e u v s : Vertex d.radical}
    (back : CriticalPath d.radical geometry u e) (hb : geometry.b d.radical=4)
    (hmid : back.walk.getVert 2=a)
    (ha : color d.radical a=false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (next : CriticalPath d.radical geometry v a)
    (hn : Ltilde d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    (Q d.radical a).relIndex ⁅Q d.radical u,Ltilde d.radical u⁆ ≤ Nat.card F := by
  have hbudget := (h.replacement_distance_four_normalized_full_kernel_seed_budget d
    back hb ha hfixed hus hvs y hy hya next hn).2.2.2
  have hfixedu := radius_fixed_at d ha back.start_color hfixed
  have hi := h.replacement_distance_four_residual_image d back hb hfixedu
    (by simpa only [hmid] using hbudget)
  simpa only [hmid] using hi

/-- The literal midpoint lower bound makes both original seed budgets
exactly q, and the same bound controls its full local normal span image. -/
theorem Input.replacement_distance_four_normalized_full_kernel_midpoint_indices
    {geometry : Geometry d.radical} {a e u v s : Vertex d.radical}
    (back : CriticalPath d.radical geometry u e) (hb : geometry.b d.radical=4)
    (hmid : back.walk.getVert 2=a)
    (ha : color d.radical a=false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (next : CriticalPath d.radical geometry v a)
    (hn : Ltilde d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a)=Nat.card F ∧
      (B d.radical u (geometry.Z_normal u)).relIndex (U d.radical a)=Nat.card F ∧
      (Q d.radical a).relIndex (localZSpan d.radical a u) ≤ Nat.card F := by
  obtain ⟨_,_,hZ,hU⟩ := h.replacement_distance_four_normalized_full_kernel_seed_budget d
    back hb ha hfixed hus hvs y hy hya next hn
  have hlo := h.replacement_path_moving_index_ge_field d back (by omega)
  rw [hmid] at hlo
  let := finite_Z d.radical a
  have hUZ := (B d.radical u (geometry.Z_normal u)).relIndex_le_of_le_right
    (U_le_Z a) index_ne_zero_of_finite
  refine ⟨le_antisymm hZ (hlo.trans hUZ),le_antisymm hU hlo,?_⟩
  have hfixedu := radius_fixed_at d ha back.start_color hfixed
  have hi := h.replacement_distance_four_root_span_image d back hb hfixedu
    (by simpa only [hmid] using hU)
  simpa only [hmid] using hi

/-- The original endpoint selector transfers the same exact full seed
budget to the opposite endpoint of the retained backward critical path. -/
theorem Input.replacement_distance_four_normalized_full_kernel_paired_indices
    {geometry : Geometry d.radical} {a e u v s : Vertex d.radical}
    (back : CriticalPath d.radical geometry u e) (hb : geometry.b d.radical=4)
    (hmid : back.walk.getVert 2=a)
    (ha : color d.radical a=false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (next : CriticalPath d.radical geometry v a)
    (hn : Ltilde d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _))
    (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hre : act d.radical r e=u) :
    (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a)=Nat.card F ∧
      (B d.radical e (geometry.Z_normal e)).relIndex (Z d.radical a)=Nat.card F := by
  have hZ := (h.replacement_distance_four_normalized_full_kernel_midpoint_indices d
    back hb hmid ha hfixed hus hvs y hy hya next hn).1
  have hra : act d.radical r a=a := hr
  have htransport :
      (B d.radical (act d.radical r e) (geometry.Z_normal _)).relIndex
          (Z d.radical (act d.radical r a)) =
        (B d.radical e (geometry.Z_normal e)).relIndex (Z d.radical a) := by
    rw [Escape.PairingControl.FirstPairing.B_act (by omega) r e back.end_color,
      Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj r⁻¹).injective]
  rw [hre,hra] at htransport
  exact ⟨hZ,htransport.symm.trans hZ⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
