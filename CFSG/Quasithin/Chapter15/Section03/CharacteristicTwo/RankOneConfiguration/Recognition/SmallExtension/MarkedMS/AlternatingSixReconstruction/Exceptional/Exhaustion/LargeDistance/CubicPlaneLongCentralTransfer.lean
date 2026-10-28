module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongImages
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneJointSlice

/-!
# Central-intersection transfer on the original cubic plane graph

A plane-edge subactor with image larger than two has the same full seed
fixer as its edge. Paired endpoint generation gives a central-index-two
bound, and a literal interior generating pair transports the central part
across the selected neighboring vertex. All claims use the original cubic
projection and retain the central attachment of both permitted covers.

Source: Meierfrankenfeld--Stellmacher (1993), (5.11)(2), pp.923--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
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

local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
private local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem plane_cover_large_fixed_index
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (P : Subgroup M) (hP : P ≤ Rg) (hcard : 2 < Nat.card (P.map π)) :
    (centralizer (P : Set M)).relIndex W₀ = 4 := by
  let := h.relative_normal
  have hdvd : (centralizer (P : Set M)).relIndex W₀ ∣ 4 := by
    rw [←plane_radical_fixed_index h e hz hk u hR]
    exact relIndex_dvd_of_le_left _ (centralizer_le hP)
  have hlo : 2 < (centralizer (P : Set M)).relIndex W₀ := by
    by_contra! hn
    have hs : fixedCodim (coverAction h e hz hk) (P.map π) ≤ 1 := by
      rw [centralizer_index_eq_fixedCodim W₀ π (CubicEven.projection_surjective h e hz hk)
        (CubicAction.moved_projection_kernel h e hz hk)] at hn
      exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hn
    have hnat : fixedCodim (naturalRepresentation (Fin 6)) (P.map π) ≤ 1 :=
      (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk)
        (naturalRepresentation (Fin 6)) (coverMap h e hz hk)
        (coverMap_surjective h e hz hk) (coverMap_equivariant h e hz hk) (P.map π)).trans hs
    have hne : P.map π ≠ ⊥ := by
      intro he
      rw [he,Subgroup.card_bot] at hcard
      omega
    obtain ⟨t,_,ht,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (P.map π) hne hnat
    rw [he,Nat.card_zpowers,ht.orderOf] at hcard
    omega
  exact eq_four_of_dvd_four hdvd hlo

include h e hz hk in
/-- Any image of order greater than two in a plane edge fixes exactly the full edge
omega-center on the endpoint seed, including all central attachments. -/
theorem plane_large_image_fixed_seed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (P : Subgroup (FreeAmalgam Rg)) (hP : P ≤ Q Rg t)
    (hindex : 2 < (Q Rg c).relIndex P) :
    Z Rg c ⊓ centralizer (P : Set (FreeAmalgam Rg)) = Z Rg t ∧
      (centralizer (P : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hc hct
  have hmP : (P.comap i).map i = P :=
    map_comap_eq_self (hP.trans (hiR ▸ map_le_range i _))
  have hPr : P.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmP,hiR]
  have hcard : 2 < Nat.card ((P.comap i).map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk _
      (h.relative_radical.isPGroup.to_le hPr)]
    rwa [←hmP,←hiQ,relIndex_map_map_of_injective _ _ hi] at hindex
  have hmove : (centralizer (P : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 := by
    have hh := plane_cover_large_fixed_index h e hz hk u hR (P.comap i) hPr hcard
    rw [←hiU,←hmP,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left]
    exact hh
  obtain ⟨hfix,hfull,_⟩ := plane_edge_full_seed_fixer h e hz hk u hR hc hct
  have hZC : Z Rg t ≤ centralizer (P : Set (FreeAmalgam Rg)) :=
    (hfix ▸ inf_le_right).trans (centralizer_le hP)
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hidx : (centralizer (P : Set (FreeAmalgam Rg))).relIndex (Z Rg c) = 4 := by
    apply Nat.le_antisymm
    · exact (relIndex_le_of_le_left hZC index_ne_zero_of_finite).trans_eq hfull
    · rw [←hmove]
      exact relIndex_le_of_le_right (DistanceEight.U_le_Z Rg c) index_ne_zero_of_finite
  have hle : Z Rg t ≤ Z Rg c ⊓ centralizer (P : Set (FreeAmalgam Rg)) :=
    le_inf (adjacent_Z_le Rg hc hct) hZC
  have hh := relIndex_mul_relIndex (Z Rg t)
    (Z Rg c ⊓ centralizer (P : Set (FreeAmalgam Rg))) (Z Rg c) hle inf_le_left
  rw [inf_relIndex_left,hidx,hfull] at hh
  exact ⟨le_antisymm (relIndex_eq_one.mp (by omega)) hle,hmove⟩

include h e hz hk in
/-- Paired endpoint generation bounds the fixed seed central index by two. -/
theorem plane_long_paired_fixed_seed_central_index
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (t : Vertex Rg) (hat : Adjacent Rg a t)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hgen : Q Rg t ⊔ Z Rg a' ⊔ Z Rg (act Rg x a') = stabilizer Rg a)
    (H : Subgroup (FreeAmalgam Rg))
    (hHZ : H ≤ Z Rg a) (hHe : H ≤ Z Rg t)
    (hHend : H ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg))) :
    (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex H ≤ 2 := by
  let C := centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
  let K := Q Rg (act Rg x a')
  have ht : color Rg t=true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hHC : H ⊓ K ≤ C := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_centralizer_iff.mp
      intro x hx
      have he := hHe hx.1
      rw [Z,if_neg (by simp [ht])] at he
      exact (mem_omegaCenter_iff.mp he).2.2
    · exact le_centralizer_iff.mp (inf_le_left.trans hHend)
    · exact le_centralizer_iff.mp (inf_le_right.trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg _ ((action_preserves_color Rg _ _).trans p.end_color)))))
  have hfix : act Rg x a = a := hx
  have hidx : K.relIndex (Z Rg a)=2 := by
    change (Q Rg (act Rg x a')).relIndex (Z Rg a)=2
    conv_lhs => rhs; rw [←hfix]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact (plane_long_critical_indices_two h e hz hk hb u hR p).1
  let := finite_Z Rg a
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hi := relIndex_le_of_le_left hHC (index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H))
  rw [inf_relIndex_left] at hi
  exact hi.trans ((relIndex_le_of_le_right hHZ index_ne_zero_of_finite).trans_eq hidx)

include h e hz hk in
/-- The central part of a seed fixer transports through the original interior generating pair. -/
theorem plane_long_central_intersection_transfer
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (H : Subgroup (FreeAmalgam Rg)) (hHc : H ≤ Z Rg (act Rg g (p.walk.getVert 2)))
    (hHend : H ≤ centralizer (V Rg a' : Set (FreeAmalgam Rg)))
    (hlarge : 2 < (Q Rg (p.walk.getVert 2)).relIndex (V Rg a')) :
    H ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (act Rg g (p.walk.getVert 2)) : Set (FreeAmalgam Rg)) := by
  let H₀ := H ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
  have hfixed : H₀.map (MulAut.conj g⁻¹).toMonoidHom = H₀ :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp (show H₀ ≤ centralizer
        (stabilizer Rg a : Set (FreeAmalgam Rg)) from inf_le_right)
          ((stabilizer Rg a).inv_mem hg)))
  have hH₂ : H₀ ≤ Z Rg (p.walk.getVert 2) := by
    have hh : H₀ ≤ Z Rg (act Rg g (p.walk.getVert 2)) := inf_le_left.trans hHc
    rw [Z_act,←hfixed] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hl : p.walk.length=sourceDistance h := p.length_eq_b
  have ha₂ : color Rg (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have h₂₃ : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have ha₃ : color Rg (p.walk.getVert 3)=true := by
    have hh := adjacent_color_ne Rg h₂₃
    rw [ha₂] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hV₃ : V Rg a' ≤ Q Rg (p.walk.getVert 3) := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) p.end_color
    rw [SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-3+2 < sourceDistance h
    omega
  have hH₃ : H₀ ≤ Z Rg (p.walk.getVert 3) :=
    (le_inf hH₂ (inf_le_left.trans hHend)).trans
      (plane_large_image_fixed_seed h e hz hk u hR ha₂ h₂₃ (V Rg a') hV₃ hlarge).1.le
  have hHC₂ : H₀ ≤ centralizer (stabilizer Rg (p.walk.getVert 2) :
      Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    refine sup_le ?_ ?_
    · apply le_centralizer_iff.mp
      apply (inf_le_right : H₀ ≤ centralizer (stabilizer Rg a : Set _)).trans
      apply centralizer_le
      intro x hx
      apply hx.2 a
      apply adjacent_symm Rg
      apply (cosetGraph_adj Rg _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    · apply le_centralizer_iff.mp
      intro x hx
      have hh := hH₃ hx
      rw [Z,if_neg (by simp [ha₃])] at hh
      exact (mem_omegaCenter_iff.mp hh).2.2
  have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hHC₂).trans
    (map_centralizer_le_centralizer_image _ _)
  change H₀.map (MulAut.conj g⁻¹).toMonoidHom ≤
    centralizer ((stabilizer Rg (p.walk.getVert 2)).map
      (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam Rg)) at hh
  rwa [hfixed,←stabilizer_act] at hh


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
