module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongImages
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusKernel

/-!
# The radius-kernel tower above four on the original cubic plane

Generating incident plane-edge kernels intersect in the original component
two-core. Their common image is central in the symmetric quotient, and the
common subgroup is a two-group; the latter fact removes only its intersection
with the cubic kernel, preserving the full odd quotient E/Q.

This identifies the first interior kernel of a critical radius. An opposite
radius of index four consequently has two exact index-two steps, and the
whole intermediate kernel has precisely the original critical commutator.
The selected path and its interior-generation and index-four hypotheses
remain explicit in these local tower lemmas.

The private natural import reuses only generic subgroup index arithmetic.
Source: Meierfrankenfeld--Stellmacher (1993), (5.11)(1), p.923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem plane_edge_derived_le_core (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    ⁅Q Rg t,Q Rg t⁆ ≤ Q Rg a := by
  have hcomm : ⁅(Rg).map π,(Rg).map π⁆ = ⊥ := by
    rw [hR]
    let := D_elementary
    let : IsElementaryAbelian 2 (D.map (MulAut.conj u).toMonoidHom) :=
      IsElementaryAbelian.map _
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hE : ⁅Rg,Rg⁆ ≤ extensionKernel h := by
    rw [←CubicAction.projection_kernel h e hz hk,←Subgroup.map_eq_bot_iff,map_commutator]
    exact hcomm
  have hQ : ⁅Rg,Rg⁆ ≤ pCore 2 M :=
    two_subgroup_le_core_of_le_extensionKernel h hz _
      (h.relative_radical.isPGroup.to_le (commutator_le_self _)) hE
  obtain ⟨i,hi,_,hiR,hiQ,_⟩ := remaining_edge_coordinates h e hz ha hat
  rw [←hiR,←hiQ,←map_commutator]
  exact map_mono hQ

include h e hz hk in
private theorem plane_two_central_mod_core_le_core
    {a : Vertex Rg} (ha : color Rg a = false)
    (N : Subgroup (FreeAmalgam Rg)) (hN : N ≤ stabilizer Rg a)
    (htwo : IsPGroup 2 N)
    (hcomm : ⁅N,stabilizer Rg a⁆ ≤ Q Rg a) : N ≤ Q Rg a := by
  obtain ⟨i,hi,hir,hiQ,_⟩ := graph_cover h e hz hk a ha
  have hE : N.comap i ≤ extensionKernel h := by
    intro y hy
    have hcentral : π y ∈ center (Equiv.Perm (Fin 6)) := by
      apply mem_center_iff.mpr
      intro z
      obtain ⟨w,rfl⟩ := CubicEven.projection_surjective h e hz hk z
      have hmem : i ⁅y,w⁆ ∈ (pCore 2 M).map i := by
        rw [map_commutatorElement,hiQ]
        exact hcomm (commutator_mem_commutator hy
          (hir ▸ (show i w ∈ i.range from ⟨w,rfl⟩)))
      have hcore : ⁅y,w⁆ ∈ pCore 2 M := (mem_map_iff_mem hi).mp hmem
      have hker : π ⁅y,w⁆ = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [CubicAction.projection_kernel h e hz hk]
        exact (show pCore 2 M ≤ extensionKernel h from le_sup_right) hcore
      rw [map_commutatorElement] at hker
      exact (commutatorElement_eq_one_iff_mul_comm.mp hker).symm
    rw [s6_center_eq_bot,mem_bot] at hcentral
    rwa [←CubicAction.projection_kernel h e hz hk,MonoidHom.mem_ker]
  have hQ := two_subgroup_le_core_of_le_extensionKernel h hz (N.comap i)
    (htwo.comap_of_injective i hi) hE
  have hm := map_mono (f := i) hQ
  rwa [map_comap_eq_self (hN.trans_eq hir.symm),hiQ] at hm

/-- Two generating incident plane kernels intersect in the original two-core.
Only a two-subgroup of the cubic covering kernel is contracted to the core. -/
theorem plane_generating_edge_kernels_inf (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a t v : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (hav : Adjacent Rg a v)
    (hgen : Q Rg t ⊔ Q Rg v = stabilizer Rg a) :
    Q Rg t ⊓ Q Rg v = Q Rg a := by
  have hlocal {w : Vertex Rg} (haw : Adjacent Rg a w) : Q Rg a ≤ Q Rg w := by
    have ht : color Rg w = true := by
      have hh := adjacent_color_ne Rg haw
      rw [ha] at hh
      cases he : color Rg w <;> simp_all
    exact Q_le_adjacent_h Rg ht haw
  apply le_antisymm _ (le_inf (hlocal hat) (hlocal hav))
  have ht : IsPGroup 2 (Q Rg t) := by
    obtain ⟨i,_,_,hiR,_⟩ := remaining_edge_coordinates h e hz ha hat
    rw [←hiR]
    exact h.relative_radical.isPGroup.map i
  apply plane_two_central_mod_core_le_core h e hz hk ha _
    (inf_le_left.trans (show Q Rg t ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat))) (ht.to_le inf_le_left)
  rw [commutator_comm,←hgen]
  apply commutator_sup_le_of_relative_normal (stabilizer Rg a)
    (Q Rg t) (Q Rg v) (Q Rg t ⊓ Q Rg v) (Q Rg a) (Q_normalized Rg a)
    (le_sup_left.trans_eq hgen) (le_sup_right.trans_eq hgen)
  · exact (commutator_mono le_rfl inf_le_left).trans (plane_edge_derived_le_core h e hz hk u hR ha hat)
  · exact (commutator_mono le_rfl inf_le_right).trans (plane_edge_derived_le_core h e hz hk u hR ha hav)


/-- The opposite radius kernel in the start core lies in the first interior core. -/
theorem plane_long_radius_kernel_le_interior
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2)) :
    V Rg a' ⊓ Q Rg a ≤ Q Rg (p.walk.getVert 2) := by
  have hl : p.walk.length=sourceDistance h := p.length_eq_b
  have ha₂ : color Rg (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have h₂₁ : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have h₂₃ : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  rw [←plane_generating_edge_kernels_inf h e hz hk u hR ha₂ h₂₁ h₂₃ hgen]
  apply le_inf
  · have ha₁ : Adjacent Rg a (p.walk.getVert 1) := by
      apply (cosetGraph_adj Rg _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    have ht : color Rg (p.walk.getVert 1)=true := by
      have hh := adjacent_color_ne Rg ha₁
      rw [p.start_color] at hh
      cases he : color Rg (p.walk.getVert 1) <;> simp_all
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht ha₁)
  · apply inf_le_left.trans
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) p.end_color
    rw [SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-3+2 < sourceDistance h
    omega


/-- Radius index four gives the exact two-step kernel tower on the original graph. -/
theorem plane_long_radius_four_kernel_tower
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hfour : (Q Rg a).relIndex (V Rg a')=4) :
    (Q Rg (p.walk.getVert 2)).relIndex (V Rg a')=2 ∧
      (Q Rg a).relIndex (V Rg a' ⊓ Q Rg (p.walk.getVert 2))=2 ∧
      V Rg a' ⊓ Q Rg (p.walk.getVert 2) =
        Z Rg a' ⊔ (V Rg a' ⊓ Q Rg a) := by
  have hl : p.walk.length=sourceDistance h := p.length_eq_b
  have hZC : Z Rg a' ≤ Q Rg (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt Rg a' ((sourceGeometry h).exists_critical a' p.end_color)
    rw [(sourceGeometry h).distance_constant a' p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < sourceDistance h
    omega
  let rev : CriticalPath Rg (sourceGeometry h) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant _ p.start_color]
          exact sourceDistance_pos h) a' p.end_color p.critical⟩
  have hescape := plane_radius_escape h e hz hk u hR rev
  change ¬ V Rg a' ≤ Q Rg
    (p.walk.reverse.getVert (p.walk.reverse.length-2)) at hescape
  rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
    show p.walk.length-(p.walk.length-2)=2 by omega] at hescape
  have hVQ := V_le_Q Rg (geometry := sourceGeometry h) p.end_color
    (show 2 < sourceDistance h by omega)
  let := finite_stabilizer Rg a'
  let : Finite (V Rg a') := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  exact Natural.Exhaustion.LargeDistance.SectionFive.index_four_kernel_tower _ _ _ _ (Z_le_VBall Rg _ 2) hZC
    (plane_long_radius_kernel_le_interior h e hz hk hb u hR p hgen)
    (plane_long_critical_indices_two h e hz hk hb u hR p).2.1
    hfour hescape

include h e hz hk in
/-- In the equality-four case, the whole interior radius kernel has exactly
the original critical commutator against the starting seed. -/
theorem plane_long_radius_four_kernel_commutator
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hfour : (Q Rg a).relIndex (V Rg a')=4) :
    ⁅V Rg a' ⊓ Q Rg (p.walk.getVert 2),Z Rg a⁆ =
      ⁅Z Rg a',Z Rg a⁆ := by
  have ht := plane_long_radius_four_kernel_tower h e hz hk hb u hR p hgen hfour
  rw [ht.2.2]
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  let J := ⁅Z Rg a',Z Rg a⁆
  have hJZ : J ≤ Z Rg a' := by
    dsimp only [J]
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le a _ p.critical.1.le).trans (Z_normalized Rg a'))
  have hQN : Q Rg a' ≤ normalizer (J : Set (FreeAmalgam Rg)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a' p.end_color))).trans (centralizer_le hJZ)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hVQ := V_le_Q Rg (geometry := sourceGeometry h) p.end_color
    (show 2 < sourceDistance h by omega)
  apply commutator_sup_le_of_relative_normal (Q Rg a')
    (Z Rg a') (V Rg a' ⊓ Q Rg a) (Z Rg a) J hQN
    ((Z_le_VBall Rg a' 2).trans hVQ) (inf_le_left.trans hVQ) le_rfl
  exact (commutator_mono inf_le_right le_rfl).trans
    (by rw [commutator_comm,Z_centralizes_Q Rg a p.start_color]; exact bot_le)


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
