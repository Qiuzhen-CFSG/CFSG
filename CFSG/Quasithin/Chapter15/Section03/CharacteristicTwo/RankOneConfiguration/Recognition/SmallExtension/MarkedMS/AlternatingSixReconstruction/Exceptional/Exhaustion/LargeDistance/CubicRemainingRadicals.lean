module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPointExclusion
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePlane
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicThompsonSelectors

/-!
# Plane Thompson choices and actual Sylow edges through the cubic quotient

The two remaining images of the prescribed odd-index radical are treated
on the original graph. Since the projection kernel is E, with |E/Q| = 3,
the ambient two-core has index 2160. The plane image therefore gives the
original radical index 270, while the Borel image gives index 135. Only
the latter makes the original radical Sylow. Faithful edge charts carry
that Sylow property to each adjacent component stabilizer.

For the plane image, both permitted full moving covers have fixed index
four under the entire radical, whose image has order eight. Thus the
whole edge is a small mover and is the unique one of maximum order. This
identifies the actual source Thompson join at both ends of any two-edge
path, without selecting independently marked graphs or discarding the
central attachment of the order-32 cover.

The whole-core and literal C.1.32 consumers discharge these Thompson and
Sylow premises. The plane and Borel distance contradictions, exceptional
core exhaustion, natural exhaustion and both reconstruction outcomes
remain with the same assembly owner. In particular, an odd covering
kernel is retained in all index calculations; it is not replaced by Q.

Source: Aschbacher--Smith C.1.31(MS2)(a), C.1.32, pp.135--136;
Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two (1993),
Section 5.0 and the maximum-order choices of (5.4), pp.912,915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem radical_core_index :
    (pCore 2 M).index = 2160 := by
  have hQE : (pCore 2 M).relIndex (extensionKernel h) = 3 := by
    change ((pCore 2 M).comap (extensionKernel h).subtype).index = 3
    rw [←pCore_subnormal_eq_comap 2
      (inferInstance : (extensionKernel h).Normal).isSubnormal]
    exact extensionKernel_core_index h hz
  have hE : (extensionKernel h).index = 720 := by
    rw [←CubicAction.projection_kernel h e hz hk,index_ker,
      MonoidHom.range_eq_top.mpr (CubicEven.projection_surjective h e hz hk),
      Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  have hh := relIndex_mul_index
    (show pCore 2 M ≤ extensionKernel h from le_sup_right)
  rw [hQE,hE] at hh
  exact hh.symm

include h e hz hk in
private theorem radical_index_mul_image :
    Nat.card ((Rg).map π) * (Rg).index = 2160 := by
  rw [CubicAction.permutation_image_card_of_two h e hz hk Rg
    h.relative_radical.isPGroup,
    relIndex_mul_index h.relative_radical.twoCore_le]
  exact radical_core_index h e hz hk

include h e hz hk in
/-- The original plane radical has index 270, with the odd covering kernel retained. -/
theorem plane_radical_index (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) :
    (Rg).index = 270 := by
  have hh := radical_index_mul_image h e hz hk
  rw [hR,card_map_of_injective (MulAut.conj u).injective,D_card] at hh
  omega

include h e hz hk in
/-- The original Borel radical has odd index 135. -/
theorem borel_radical_index (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (Rg).index = 135 := by
  have hh := radical_index_mul_image h e hz hk
  rw [hR,card_map_of_injective (MulAut.conj u).injective,borel_order] at hh
  omega

include h e hz hk in
/-- The Borel image makes the original radical Sylow; this is a conclusion. -/
theorem borel_radical_isSylow (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ∃ T : Sylow 2 M, (T : Subgroup M) = Rg := by
  exact ⟨h.relative_radical.isPGroup.toSylow (by
    rw [borel_radical_index h e hz hk u hR]; decide),rfl⟩

include h e hz hk in
/-- A plane image keeps the original radical strictly below every Sylow overgroup. -/
theorem plane_radical_not_sylow (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) :
    ¬ ∃ T : Sylow 2 M, (T : Subgroup M) = Rg := by
  rintro ⟨T,hT⟩
  have hh := T.not_dvd_index
  rw [hT,plane_radical_index h e hz hk u hR] at hh
  exact hh (by decide)

include h e hz hk in
/-- On either entire moving cover, the original plane radical has fixed index four. -/
theorem plane_radical_fixed_index (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) :
    (centralizer (Rg : Set M)).relIndex W = 4 := by
  have hh := cubic_cover_movement_bounds h e hz hk Rg
  rw [hR,fixedCodim_map_conj,fixedCodim_map_conj,SixCorePlane.cube_eq,
    fixedCodim_D.2.2.2,fixedCodim_D.2.2.1] at hh
  omega

include h e hz in
private theorem remaining_edge_coordinates
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
      ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧
        i.range = stabilizer Rg c ∧ (Rg).map i = Q Rg t ∧ (pCore 2 M).map i = Q Rg c ∧
        (W).map i = U Rg c := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective Rg),?_,?_,?_,?_⟩
      · have hh := stabilizer_act Rg g (alpha Rg)
        dsimp only [i]
        rw [MonoidHom.range_comp]
        change (Mbar Rg).map (MulAut.conj g⁻¹).toMonoidHom = _
        simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using hh.symm
      · have h := Q_act Rg g (beta Rg)
        rw [Q_beta] at h
        simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using h.symm
      · have hh := Q_act Rg g (alpha Rg)
        rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
        simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
      · have hh := U_act Rg g (alpha Rg)
        rw [←graph_U_map h e hz] at hh
        simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
    · rw [hg.1] at hc
      cases hc

include h e hz hk in
/-- The plane edge itself is the unique maximum-order small mover. -/
theorem plane_edge_maximal_offenders (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    edgeMaximalOffenders c t = {Q Rg t} ∧
      (centralizer (Q Rg t : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 ∧
      (Q Rg c).relIndex (Q Rg t) = 8 := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := remaining_edge_coordinates h e hz hc hct
  have hf : (centralizer (Q Rg t : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 := by
    rw [←hiR,←hiW,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left]
    exact plane_radical_fixed_index h e hz hk u hR
  have hiq : (Q Rg c).relIndex (Q Rg t) = 8 := by
    rw [←hiQ,←hiR,relIndex_map_map_of_injective _ _ hi,
      ←CubicAction.permutation_image_card_of_two h e hz hk Rg h.relative_radical.isPGroup,
      hR,card_map_of_injective (MulAut.conj u).injective,D_card]
  have hsmall : edgeSmallMover c t (Q Rg t) := by
    exact ⟨le_rfl,by rw [hf,hiq]; decide,by rw [hf]⟩
  have hfinite : Finite (Q Rg t) := by
    rw [←hiR]
    exact Finite.of_surjective (i.subgroupMap Rg) (i.subgroupMap_surjective Rg)
  let := hfinite
  refine ⟨?_,hf,hiq⟩
  ext A
  constructor
  · intro hA
    exact Set.mem_singleton_iff.mpr
      (eq_of_le_of_card_ge hA.1.1 (hA.2 _ hsmall))
  · rintro rfl
    exact ⟨hsmall,fun B hB => card_le_of_le hB.1⟩

include h e hz hk in
/-- The literal source Thompson join is the full edge in the plane branch. -/
theorem plane_edgeOffenderJoin_eq (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    edgeOffenderJoin c t = Q Rg t := by
  rw [edgeOffenderJoin,(plane_edge_maximal_offenders h e hz hk u hR hc hct).1,
    sSup_singleton]

include h e hz hk in
/-- Across either end of the same plane edge the source joins agree with its kernel. -/
theorem plane_adjacent_thompson_choices (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) :
    edgeMaximalOffenders a t = {Q Rg t} ∧
      edgeMaximalOffenders c t = {Q Rg t} ∧
      edgeOffenderJoin a t = edgeOffenderJoin c t := by
  exact ⟨(plane_edge_maximal_offenders h e hz hk u hR ha hat).1,
    (plane_edge_maximal_offenders h e hz hk u hR hc hct).1,
    (plane_edgeOffenderJoin_eq h e hz hk u hR ha hat).trans
      (plane_edgeOffenderJoin_eq h e hz hk u hR hc hct).symm⟩

include h e hz hk in
/-- In the Borel branch the literal edge kernel is Sylow in each adjacent
component stabilizer; its local index includes the original cubic factor. -/
theorem borel_edge_sylow (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    (Q Rg t).relIndex (stabilizer Rg c) = 135 ∧
      ∃ T : Sylow 2 (stabilizer Rg c),
        (T : Subgroup (stabilizer Rg c)).map (stabilizer Rg c).subtype = Q Rg t := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := remaining_edge_coordinates h e hz hc hct
  have hind : (Q Rg t).relIndex (stabilizer Rg c) = 135 := by
    rw [←hiR,←hir,MonoidHom.range_eq_map,
      relIndex_map_map_of_injective _ _ hi,relIndex_top_right]
    exact borel_radical_index h e hz hk u hR
  have htwo : IsPGroup 2 (Q Rg t) := hiR ▸ h.relative_radical.isPGroup.map i
  have hle : Q Rg t ≤ stabilizer Rg c := by
    rw [←hiR,←hir]
    exact map_le_range i Rg
  refine ⟨hind,htwo.comap_subtype.toSylow (by
    change ¬ 2 ∣ (Q Rg t).relIndex (stabilizer Rg c)
    rw [hind]; decide),?_⟩
  exact map_subgroupOf_eq_of_le hle

omit hk in
include h e hz in
/-- Whole-core assembly now supplies the plane Thompson choice or the
actual local Sylow hypotheses, on the same graph and projection. -/
theorem coreExhaustion_or_cubic_plane_thompson_or_sylow :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            D.map (MulAut.conj u).toMonoidHom ∧
          (Rg).index = 270 ∧
          ∀ c t : Vertex Rg, color Rg c = false → Adjacent Rg c t →
            edgeMaximalOffenders c t = {Q Rg t} ∧
              edgeOffenderJoin c t = Q Rg t ∧
              (centralizer (Q Rg t : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 ∧
              (Q Rg c).relIndex (Q Rg t) = 8) ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
            borel.map (MulAut.conj u).toMonoidHom ∧
          (Rg).index = 135 ∧
          (∃ T : Sylow 2 M, (T : Subgroup M) = Rg) ∧
          ∀ c t : Vertex Rg, color Rg c = false → Adjacent Rg c t →
            ∃ T : Sylow 2 (stabilizer Rg c),
              (T : Subgroup (stabilizer Rg c)).map (stabilizer Rg c).subtype = Q Rg t) := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hplane | hborel⟩
  · exact Or.inl hex
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hplane,
      plane_radical_index h e hz hk u hplane,?_⟩⟩
    intro c t hc hct
    have hh := plane_edge_maximal_offenders h e hz hk u hplane hc hct
    exact ⟨hh.1,plane_edgeOffenderJoin_eq h e hz hk u hplane hc hct,hh.2⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hborel,
      borel_radical_index h e hz hk u hborel,borel_radical_isSylow h e hz hk u hborel,
      fun c t hc hct => (borel_edge_sylow h e hz hk u hborel hc hct).2⟩⟩

omit hk in
include h e hz in
/-- The literal C.1.32 application retains both covers and discharges the
plane Thompson and Borel local Sylow premises. Their exclusions remain. -/
theorem rankTwo_or_cubic_plane_thompson_or_sylow :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            D.map (MulAut.conj u).toMonoidHom ∧
          (Rg).index = 270 ∧
          ∀ c t : Vertex Rg, color Rg c = false → Adjacent Rg c t →
            edgeMaximalOffenders c t = {Q Rg t} ∧
              edgeOffenderJoin c t = Q Rg t ∧
              (centralizer (Q Rg t : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 ∧
              (Q Rg c).relIndex (Q Rg t) = 8) ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
            borel.map (MulAut.conj u).toMonoidHom ∧
          (Rg).index = 135 ∧
          (∃ T : Sylow 2 M, (T : Subgroup M) = Rg) ∧
          ∀ c t : Vertex Rg, color Rg c = false → Adjacent Rg c t →
            ∃ T : Sylow 2 (stabilizer Rg c),
              (T : Subgroup (stabilizer Rg c)).map (stabilizer Rg c).subtype = Q Rg t) :=
  (coreExhaustion_or_cubic_plane_thompson_or_sylow h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
