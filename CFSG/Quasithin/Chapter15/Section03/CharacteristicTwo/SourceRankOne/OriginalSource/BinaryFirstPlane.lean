module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.BinaryCoefficients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import Theory.GroupAction.FourElementTwoAction
public import Theory.GroupAction.Quadratic
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The original first fixed line in the binary large-core branch

The source core lies in S. Its action on the four-group V₁ is therefore
quadratic, so [V₁,Q] lies in Z(Q) and in the first Sylow-fixed line.
The marked natural quotient of Z(Q) has no Y₊-fixed vector. Consequently
this displacement centralizes L. If it is nontrivial it is the entire
first line; if it is trivial the original cocycle argument contradicts
the V₁ normalizer bound. Thus L centralizes the original first line in
either case, without assuming that the original two-core fixes the MS
replacement's central factor.

Source: Aschbacher--Smith 15.3.29 and the argument of 15.3.31,
printed pp.1131--1132; the local-center model of C.1.34(4).
-/

public noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryFirstPlane
open RankOneConfiguration SmallExtension SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass} {d : LocalData G}
  {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)

/-- The action of the actual Sylow plane stabilizer is quadratic on V₁. -/
theorem first_plane_displacement_fixed : ⁅d.V₁,d.S⁆ ≤ d.ZS ⊓ d.V₁ := by
  have hn : d.S ≤ normalizer (d.V₁ : Set G) := inf_le_right
  let : Normalizes d.S d.V₁ := ⟨hn⟩
  have hq := two_group_action_on_four_is_quadratic (d.T.isPGroup'.to_le
    (show d.S ≤ (d.T : Subgroup G) from inf_le_left)) (d.action.card_plane 1)
  have hfix := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hq
  rw [← commutatorAction_subgroup_conj_map_eq_commutator d.V₁ d.S hn]
  rintro x ⟨v,hv,rfl⟩
  refine ⟨⟨d.action.plane_le 1 v.property, ?_⟩,v.property⟩
  intro a ha
  have he := congrArg Subtype.val ((hfix hv) (⟨a,ha⟩ : d.S))
  change a * (v : G) * a⁻¹ = (v : G) at he
  exact mul_inv_eq_iff_eq_mul.mp he

omit [Finite G] in
include s in
private theorem core_le_sylow : extensionCore c.L ≤ d.S := by
  have hi : extensionCore c.L ≤ I.pCoreIn 2 := by
    rw [extensionCore_eq_overgroup d c s.contains s.normal]
    exact le_normalizer_iff_commutator_le_left.mp
      ((component_le c).trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
  exact hi.trans (s.sylow_eq ▸ pCoreIn_le_sylow I s.sylow)

include s in
/-- The actual core displacement lies both in its center and in the first fixed line. -/
theorem first_plane_core_displacement :
    ⁅d.V₁,extensionCore c.L⁆ ≤ coreCenter c.L ⊓ (d.ZS ⊓ d.V₁) := by
  have hline := (commutator_mono le_rfl (core_le_sylow s)).trans
    (first_plane_displacement_fixed (d := d))
  have hIQ := normalizes_extensionCore
    ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal)
  refine le_inf (le_inf ?_ ?_) hline
  · exact le_normalizer_iff_commutator_le_right.mp (s.first_plane_control.1.trans hIQ)
  · exact (hline.trans (inf_le_left.trans inf_le_right)).trans
      (centralizer_le (core_le_sylow s))

private def recoordinate (m : CenterModel c.L natural) (a : SL) : CenterModel c.L natural where
  quotientIso := m.quotientIso.trans (MulAut.conj a)
  moduleIso := m.moduleIso.trans (LinearModels.FullCenter.actionEquiv (ρ := natural) a)
  intertwining l z := by
    change Multiplicative.ofAdd (natural a (m.coordinates (centerConjugate c.L l z)).toAdd) = _
    rw [m.coordinates_conjugate]
    apply congrArg Multiplicative.ofAdd
    change natural a (natural (m.actorMap l) (m.coordinates z).toAdd) =
      natural (a * m.actorMap l * a⁻¹) (natural a (m.coordinates z).toAdd)
    rw [map_mul,map_mul]
    simp only [Module.End.mul_apply,inv_self_apply]
  core_centralizes := m.core_centralizes

omit [Finite G] in
private theorem fixed_center_centralizes (m : CenterModel c.L natural)
    (ht : planeTransvection ∈ (d.Yplus.subgroupOf c.L).map m.actorMap)
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.actorMap) :
    coreCenter c.L ⊓ centralizer (d.Yplus : Set G) ≤ centralizer (c.L : Set G) := by
  intro z hz
  let zC : coreCenter c.L := ⟨z,hz.1⟩
  apply (m.coordinates_eq_one_iff zC).mp
  apply Multiplicative.toAdd.injective
  apply fixed_marked_matrices_eq_zero
  · obtain ⟨l,hl,he⟩ := ht
    have hc : centerConjugate c.L l zC = zC := by
      apply Subtype.ext
      change (l : G) * z * (l : G)⁻¹ = z
      rw [mem_centralizer_iff.mp hz.2 l hl,mul_inv_cancel_right]
    have hh := congrArg Multiplicative.toAdd (m.coordinates_conjugate l zC)
    rw [hc,he] at hh
    exact hh.symm
  · obtain ⟨l,hl,he⟩ := hr
    have hc : centerConjugate c.L l zC = zC := by
      apply Subtype.ext
      change (l : G) * z * (l : G)⁻¹ = z
      rw [mem_centralizer_iff.mp hz.2 l hl,mul_inv_cancel_right]
    have hh := congrArg Multiplicative.toAdd (m.coordinates_conjugate l zC)
    rw [hc,he] at hh
    exact hh.symm
/-- The original first fixed line has order two. -/
theorem firstLine_card : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2 := by
  have heq : d.ZS ⊓ d.V₁ = fixedPlane d.V₁ d.S := by
    ext x
    exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨d.action.plane_le 1 hx.1,hx.2⟩,hx.1⟩⟩
  rw [heq]
  exact d.action.card_plane_fixed_planeStabilizer d.T d.sylow_le 1


include s in
private theorem firstLine_action_of_marked_center
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (m : CenterModel c.L natural)
    (ht : planeTransvection ∈ (d.Yplus.subgroupOf c.L).map m.actorMap)
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.actorMap) :
    ⁅d.V₁,extensionCore c.L⁆ = d.ZS ⊓ d.V₁ ∧
      d.ZS ⊓ d.V₁ ≤ centralizer (c.L : Set G) := by
  have hVI := s.first_plane_control.1
  have hVY := s.first_plane_control.2.1
  have hCC := fixed_center_centralizes m ht hr
  have hdisp := first_plane_core_displacement s
  have hcentral : ⁅d.V₁,extensionCore c.L⁆ ≤ centralizer (c.L : Set G) :=
    (le_inf (hdisp.trans inf_le_left)
      ((hdisp.trans (inf_le_right.trans inf_le_right)).trans hVY)).trans hCC
  by_cases he : ⁅d.V₁,extensionCore c.L⁆ = ⊥
  · have hVQ := commutator_eq_bot_iff_le_centralizer.mp he
    have hstar := s.binary_star_centralizer_of_coefficients m ht hr
    have hVL : ⁅d.V₁,c.L⁆ ≤ extensionCore c.L :=
      (commutator_mono (le_inf hVI hVY) le_rfl).trans
        (s.commutator_le_core_of_star_centralizer hstar)
    have hVZ : ⁅d.V₁,c.L⁆ ≤ coreCenter c.L := le_inf hVL
      ((commutator_mono hVQ le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          ((normalizes_extensionCore c.L.le_normalizer).trans
            (normalizer_le_normalizer_centralizer _))))
    have hf := centralizes_of_detected_model m
      (component_isPerfect_of_containment d c s.contains) hVZ hVQ d.Yplus hVY
      (detectedOn_of_marked_matrices _ ht hr)
    exact False.elim (c.outside ((le_centralizer_iff.mp hf).trans
      ((Subgroup.centralizer_le_normalizer _).trans s.first_plane_control.2.2)))
  · have hcard := firstLine_card (d := d)
    have heq : ⁅d.V₁,extensionCore c.L⁆ = d.ZS ⊓ d.V₁ :=
      eq_of_le_of_card_ge (hdisp.trans inf_le_right) (by
        rw [hcard]
        exact (Subgroup.one_lt_card_iff_ne_bot _).mpr he)
    exact ⟨heq,heq ▸ hcentral⟩

include s in
/-- The original first plane moves the core by precisely its fixed line, and L
centralizes that line. The full core-center quotient is the actual source model. -/
theorem firstLine_action_of_centerModel
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : CenterModel c.L natural) :
    ⁅d.V₁,extensionCore c.L⁆ = d.ZS ⊓ d.V₁ ∧
      d.ZS ⊓ d.V₁ ≤ centralizer (c.L : Set G) := by
  let W := MarkedModelAssembly.G2Coordinates.quotientPlane m d.V₂
  have hi := MarkedModelAssembly.G2Coordinates.planeMap_injective m
    s.plane_le_coreCenter s.contains (s.line.plane_fixed_trivial d)
  have hc : Nat.card W = 4 :=
    (MarkedModelAssembly.G2Coordinates.quotientPlane_card m s.plane_le_coreCenter hi).trans
      (d.action.card_plane _)
  have hd : Module.finrank (ZMod 2) W = 2 := MarkedModelAssembly.plane_dimension W hc
  have hn : d.M ⊓ c.L ≤ normalizer (d.V₂ : Set G) := by
    rw [s.component_parabolic]
    exact inf_le_right
  have hp : ((d.M ⊓ c.L).subgroupOf c.L).map m.actorMap =
      LinearModels.PlaneGeometry.stabilizer W := by
    apply Subgroup.eq_of_le_of_card_ge
      (MarkedModelAssembly.G2Coordinates.quotientPlane_stabilized m s.plane_le_coreCenter hn)
    change Nat.card (LinearModels.PlaneGeometry.stabilizer W) ≤ _
    rw [s.binary_centerModel_parabolic_card hm m,natural_plane_stabilizer_card W hd]
  obtain ⟨a,ha⟩ := LinearModels.PlaneGeometry.exists_plane_coordinates W hd
  have hY : d.Yplus.subgroupOf c.L = (primeToResidual 3 ((d.M ⊓ c.L).subgroupOf c.L)).map
      ((d.M ⊓ c.L).subgroupOf c.L).subtype := by
    rw [s.component_residual]
    apply Subgroup.map_injective (f := c.L.subtype) Subtype.val_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right),
      map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨ht,hr⟩ := LinearModels.PlaneGeometry.marked_mem_image m.actorMap
    ((d.M ⊓ c.L).subgroupOf c.L) (d.Yplus.subgroupOf c.L) hY W hp a ha
  exact firstLine_action_of_marked_center s (recoordinate m a) ht hr

include s in
/-- The full fixed subgroup in the original Sylow center is the first line. -/
theorem firstLine_fixed_eq_of_centerModel
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : CenterModel c.L natural) :
    d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁ := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le s.contains)).trans
      (EightGeometry.NaturalModule.FixedGeometry.yplus_fixed_eq_firstLine d
        s.rank s.yRank s.line.plane_full.symm).le
  · exact le_inf inf_le_left (firstLine_action_of_centerModel s hm m).2


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryFirstPlane
