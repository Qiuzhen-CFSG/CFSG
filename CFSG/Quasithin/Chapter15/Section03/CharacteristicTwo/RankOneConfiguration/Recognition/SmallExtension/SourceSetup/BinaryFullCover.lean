module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCenterCoefficients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.BinaryCoefficients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.CoverDuality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearThree
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover.CommutatorLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.Reduction

/-!
# The original binary full-cover contradiction

The full distance-four core supplies a natural quotient of its entire center,
with the actual component-central kernel retained. Transport to the ambient
component preserves the original marking. The source four-group maps injectively
to a natural plane, and the actual parabolic image has order24, hence is its
full stabilizer. Its marked residual detects both natural cocycles and the dual
of the doubled-dual representation. Full-cover duality then generates the whole
core, including the fixed kernel. The literal commutator lift puts that core in
Y₊. Consequently C_I(Y₊) centralizes the core, and natural cocycle detection
forces it to centralize the component, contradicting the first-plane normalizer.

Source: Aschbacher--Smith C.1.34(3) and 15.3.31, printed pp.136--137 and1132.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover CentralCover.LinearThree ChapterC
namespace BinaryCoverCoordinates
variable {G : Type*} [Group G] {L : Subgroup G}

def centerEmbedding : center (blockU L) →* coreCenter L where
  toFun z := ⟨(z.val : L), by
    refine ⟨?_,?_⟩
    · rw [← BlockModels.blockU_map]
      exact mem_map_of_mem _ z.val.property
    · apply mem_centralizer_iff.mpr
      intro y hy
      rw [← BlockModels.blockU_map] at hy
      obtain ⟨u,hu,rfl⟩ := hy
      exact congrArg (fun w : blockU L => ((w : L) : G))
        (mem_center_iff.mp z.property ⟨u,hu⟩)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem centerEmbedding_bijective : Function.Bijective (centerEmbedding (L := L)) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : coreCenter L => (z : G)) h
  · intro z
    have hz := z.property.1
    rw [← BlockModels.blockU_map] at hz
    obtain ⟨u,hu,he⟩ := hz
    refine ⟨⟨⟨u,hu⟩,mem_center_iff.mpr ?_⟩,Subtype.ext he⟩
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hc := mem_centralizer_iff.mp z.property.2 (x : L)
      (show (x : L).val ∈ extensionCore L from
        BlockModels.blockU_map L ▸ mem_map_of_mem L.subtype x.property)
    change u.val = (z : G) at he
    change ((x : L) : G) * u.val = u.val * ((x : L) : G)
    rwa [he]

def centerEquiv : center (blockU L) ≃* coreCenter L :=
  MulEquiv.ofBijective centerEmbedding centerEmbedding_bijective

theorem centerEquiv_val (z : center (blockU L)) :
    (centerEquiv z : G) = (z.val : L) := rfl

theorem centerEquiv_symm_val (z : coreCenter L) :
    (((centerEquiv.symm z).val : L) : G) = z :=
  congrArg Subtype.val (centerEquiv.apply_symm_apply z)

variable (h : BinaryMS.FullCoreDoubleDualCover L)

def coefficients : coreCenter L →* Multiplicative Space :=
  h.centerProjection.comp centerEquiv.symm.toMonoidHom

theorem coefficients_kernel : (coefficients h).ker = centerKernel L := by
  ext z
  change h.centerProjection (centerEquiv.symm z) = 1 ↔ (z : G) ∈ centralizer (L : Set G)
  rw [h.centerProjection_eq_one_iff,mem_center_iff,mem_centralizer_iff]
  constructor
  · intro hz l hl
    have he := congrArg Subtype.val (hz ⟨l,hl⟩)
    change l * (((centerEquiv.symm z).val : L) : G) =
      (((centerEquiv.symm z).val : L) : G) * l at he
    simpa only [centerEquiv_symm_val] using he
  · intro hz l
    apply Subtype.ext
    change l.val * (((centerEquiv.symm z).val : L) : G) =
      (((centerEquiv.symm z).val : L) : G) * l.val
    rw [centerEquiv_symm_val]
    exact hz l l.property

/-- The actual full-cover center gives the literal ambient coefficient quotient. -/
def centerModel : CenterModel L natural where
  quotientIso := h.marking
  moduleIso := (QuotientGroup.quotientMulEquivOfEq (coefficients_kernel h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (coefficients h)
      (h.centerProjection_surjective.comp centerEquiv.symm.surjective))
  intertwining l z := by
    change h.centerProjection (centerEquiv.symm (centerConjugate L l z)) =
      Multiplicative.ofAdd (natural (h.marking (QuotientGroup.mk' _ l))
        (h.centerProjection (centerEquiv.symm z)).toAdd)
    apply Multiplicative.toAdd.injective
    let x : h.layer := ⟨(centerEquiv.symm z).val,
      h.center_le (mem_map_of_mem _ (centerEquiv.symm z).property)⟩
    have he := h.action l x
    convert he using 1
    · apply congrArg (fun y : h.layer => (h.projection y).toAdd)
      apply Subtype.ext
      apply Subtype.ext
      change (((centerEquiv.symm (centerConjugate L l z)).val : L) : G) =
        l.val * (((centerEquiv.symm z).val : L) : G) * l.val⁻¹
      rw [centerEquiv_symm_val,centerEquiv_symm_val]
      rfl
    · rfl
  core_centralizes := by
    rintro _ ⟨r,hr,rfl⟩
    apply mem_centralizer_iff.mpr
    intro z hz
    let zC : coreCenter L := ⟨z,hz⟩
    have he := congrArg Subtype.val (h.core_centralizes_center r hr (centerEquiv.symm zC))
    change r.val * (((centerEquiv.symm zC).val : L) : G) * r.val⁻¹ =
      (((centerEquiv.symm zC).val : L) : G) at he
    rw [centerEquiv_symm_val] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

end BinaryCoverCoordinates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

public noncomputable section
open Subgroup Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover CentralCover.LinearThree
namespace ContainedCoreModels

private def graphPair : (Space × Space) ≃ₗ[ZMod 2]
    (Module.Dual (ZMod 2) Space × Module.Dual (ZMod 2) Space) :=
  BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv.prodCongr
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv

private theorem graphPair_action (a : SL) (v : Space × Space) :
    graphPair (ChapterC.BinaryMS.dualPair a v) =
      (natural.dual.prod natural.dual) a (graphPair v) := by
  apply Prod.ext
  · exact LinearMap.congr_fun
      (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' a) v.1
  · exact LinearMap.congr_fun
      (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' a) v.2

private def graphEvaluation : (Space × Space) ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) (Space × Space) :=
  (((Module.evalEquiv (ZMod 2) Space).prodCongr (Module.evalEquiv (ZMod 2) Space)).trans
    (Module.dualProdDualEquivDual (ZMod 2) _ _)).trans graphPair.dualMap

private theorem graphEvaluation_action (a : SL) (v : Space × Space) :
    graphEvaluation ((natural.prod natural) a v) =
      ChapterC.BinaryMS.dualPair.dual a (graphEvaluation v) := by
  apply LinearMap.ext
  intro w
  change (graphPair w).1 (natural a v.1) + (graphPair w).2 (natural a v.2) =
    (graphPair (ChapterC.BinaryMS.dualPair a⁻¹ w)).1 v.1 +
      (graphPair (ChapterC.BinaryMS.dualPair a⁻¹ w)).2 v.2
  rw [graphPair_action]
  change (graphPair w).1 (natural a v.1) + (graphPair w).2 (natural a v.2) =
    (graphPair w).1 (natural ((a⁻¹)⁻¹) v.1) + (graphPair w).2 (natural ((a⁻¹)⁻¹) v.2)
  rw [inv_inv]

/-- The actual coordinate doubled-dual action is detected on the marked residual. -/
theorem graph_double_dual_detected (B : Subgroup SL)
    (ht : planeTransvection ∈ B) (hr : planeRotation ∈ B) :
    DetectedOn ChapterC.BinaryMS.dualPair.dual B := by
  refine detectedOn_transport ChapterC.BinaryMS.dualPair.dual (natural.prod natural)
    (MulEquiv.refl SL) graphEvaluation.symm ?_ B ?_
  · intro a v
    apply graphEvaluation.injective
    rw [graphEvaluation.apply_symm_apply,graphEvaluation_action,
      graphEvaluation.apply_symm_apply]
    rfl
  · change DetectedOn (natural.prod natural) (B.map (MonoidHom.id SL))
    rw [Subgroup.map_id]
    exact detectedOn_two_natural B ht hr

end ContainedCoreModels
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open Subgroup Representation Representation.OneCohomology
open CentralCover CentralCover.LinearThree

private theorem detectedOn_conjugate {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL V) (B : Subgroup SL) (a : SL)
    (h : DetectedOn ρ (B.map (MulAut.conj a).toMonoidHom)) : DetectedOn ρ B := by
  apply detectedOn_transport ρ ρ (MulAut.conj a)
    (LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)) _ B h
  intro b v
  change ρ a (ρ b v) = ρ (a * b * a⁻¹) (ρ a v)
  rw [map_mul,map_mul]
  simp only [Module.End.mul_apply,inv_self_apply]

private theorem natural_stabilizer_card (W : Submodule (ZMod 2) Space)
    (hd : Module.finrank (ZMod 2) W = 2) :
    Nat.card (LinearModels.PlaneGeometry.stabilizer W) = 24 := by
  obtain ⟨a,ha⟩ := LinearModels.PlaneGeometry.exists_plane_coordinates W hd
  have he := LinearModels.PlaneGeometry.stabilizer_map_conj W a ha
  have hcan : LinearModels.PlaneGeometry.stabilizer LinearModels.PlaneGeometry.plane =
      Matrix.PSL3Two.lineParabolicSL := by
    ext g
    rw [Matrix.PSL3Two.lineParabolicSL, MulAction.mem_stabilizer_set]
    rfl
  have hc : Nat.card ((LinearModels.PlaneGeometry.stabilizer W).map
      (MulAut.conj a).toMonoidHom) = Nat.card (LinearModels.PlaneGeometry.stabilizer W) :=
    card_map_of_injective (MulAut.conj a).injective
  rw [he,hcan,Matrix.PSL3Two.card_lineParabolicSL] at hc
  exact hc.symm

namespace SourceData
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass} {d : LocalData G}
  {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)
include s
omit [Finite G] in
private theorem binary_coefficient_parabolic_card
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L) (m : CenterModel c.L natural) :
    Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map m.actorMap) = 24 := by
  let q := coreQuotientEquivStar d c s.normal s.sylow s.sylow_eq
  let f := q.symm.trans m.quotientIso
  have ha : m.actorMap = f.toMonoidHom.comp (componentMap d c) := by
    apply MonoidHom.ext
    intro l
    change m.quotientIso (QuotientGroup.mk' (pCore 2 c.L) l) =
      m.quotientIso (q.symm (componentMap d c l))
    rw [← coreQuotientEquivStar_apply d c s.normal s.sylow s.sylow_eq,
      q.symm_apply_apply]
  rw [ha, ← map_map, MarkedModelAssembly.componentMap_parabolic_image,
    card_map_of_injective f.injective]
  apply MarkedMS.Constituents.SourceReduction.marked_intersection_card_of_star_card d c hm
  exact (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.card_SL


/-- The actual marked source plane excludes the full distance-four core cover,
with its component-central kernel retained throughout. -/
theorem binary_fullCover_false
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (h : ChapterC.BinaryMS.FullCoreDoubleDualCover c.L) : False := by
  let m := BinaryCoverCoordinates.centerModel h
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
    rw [s.binary_coefficient_parabolic_card hm m,natural_stabilizer_card W hd]
  obtain ⟨a,ha⟩ := LinearModels.PlaneGeometry.exists_plane_coordinates W hd
  have hY : d.Yplus.subgroupOf c.L = (primeToResidual 3 ((d.M ⊓ c.L).subgroupOf c.L)).map
      ((d.M ⊓ c.L).subgroupOf c.L).subtype := by
    rw [s.component_residual]
    apply Subgroup.map_injective (f := c.L.subtype) Subtype.val_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right),
      map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨ht,hr⟩ := LinearModels.PlaneGeometry.marked_mem_image m.actorMap
    ((d.M ⊓ c.L).subgroupOf c.L) (d.Yplus.subgroupOf c.L) hY W hp a ha

  let B := (d.Yplus.subgroupOf c.L).map m.actorMap
  have ht' : planeTransvection ∈ B.map (MulAut.conj a).toMonoidHom := by
    simpa only [B,map_map] using ht
  have hr' : planeRotation ∈ B.map (MulAut.conj a).toMonoidHom := by
    simpa only [B,map_map] using hr
  have hnat : DetectedOn natural B := detectedOn_conjugate natural B a
    (detectedOn_of_marked_matrices _ ht' hr')
  have hdual : DetectedOn ChapterC.BinaryMS.dualPair.dual B :=
    detectedOn_conjugate ChapterC.BinaryMS.dualPair.dual B a
      (ContainedCoreModels.graph_double_dual_detected _ ht' hr')
  have hgen := ContainedCoreModels.cover_coinvariants_of_detected_dual h.cover h.isCover B hdual
  have hQ : extensionCore c.L = ⁅extensionCore c.L,d.Yplus⁆ := by
    have he := congrArg (fun U : Subgroup c.L => U.map c.L.subtype)
      (h.core_eq_commutator_of_coinvariants (d.Yplus.subgroupOf c.L) hgen)
    rwa [map_commutator,BlockModels.blockU_map,map_subgroupOf_eq_of_le s.contains] at he
  have hQY : extensionCore c.L ≤ d.Yplus := by
    rw [hQ]
    exact (ContainedCoreModels.core_commutator_le_yplus_core s).trans (pCoreIn_le 2 d.Yplus)
  have hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) :=
    inf_le_right.trans (centralizer_le hQY)
  let : (actionKernel I c.L).Normal := actionKernel_normal
    ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal)
  have hzero := centralizerImage_eq_bot_of_detected_model d c s.contains s.normal m
    (specialLinearNatural_injective 3) hDQ hnat
  have hDL := (plusImage_eq_bot_iff inf_le_left).mp hzero
  obtain ⟨hVI,hVY,hN⟩ := s.first_plane_control
  apply c.outside
  exact (le_centralizer_iff.mp ((le_inf hVI hVY).trans hDL)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)

end SourceData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
