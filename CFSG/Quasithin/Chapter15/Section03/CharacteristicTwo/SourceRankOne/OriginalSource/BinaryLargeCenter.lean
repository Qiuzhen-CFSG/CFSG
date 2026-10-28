module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCoefficients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.BinaryFullCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryDistanceEight

/-!
# The original large-distance center model

The earlier MS core-factor data give a natural quotient of the entire center of
the original component's commutator core. Its component-central kernel is retained
under the literal inclusion into the outside group. The source four-group maps
injectively to a natural plane; the small-parabolic marking then supplies the
coefficient actors for the central-cover calculation.

The final source application leaves precisely the action of C_I(Yplus) on the
whole commutator core explicit. Prescribed replacement supplies its other earlier
MS inputs without asserting that the original two-core fixes the local H factor.

Source: Aschbacher--Smith C.1.34(4), printed pp.136--137, and 15.3.31,
printed p.1132; Meierfrankenfeld--Stellmacher (1993), section 7.
-/

public noncomputable section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryLargeCenter
open RankOneConfiguration.SmallExtension RankOneConfiguration.SmallExtension.CentralCover
  ChapterC BinaryMS.MS93
universe u
variable {G J : Type u} [Group G] [Group J] [Finite J]
  {A : Subgroup G} {κ : GroupClass.{u}} {L R : Subgroup J} {h : BinaryMS.Input κ L R}
  (t : InputSetup h)
  (common : CommonFacts t.reduction.radical t.source t.geometry)
  (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)

omit [Finite J] in
private theorem block_map (e : A ≃* L) : (blockU A).map e.toMonoidHom = blockU L := by
  rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
private noncomputable def blockEquiv (e : A ≃* L) : blockU A ≃* blockU L :=
  (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr (block_map e))

private noncomputable def centerTransfer (e : A ≃* L) : coreCenter A ≃* center (blockU L) :=
  BinaryCoverCoordinates.centerEquiv.symm.trans (centerCongr (blockEquiv e))

omit [Finite J] in
private theorem centerTransfer_val (e : A ≃* L) (z : coreCenter A) :
    ((centerTransfer e z).val : L) =
      e (((BinaryCoverCoordinates.centerEquiv.symm z).val) : A) := rfl

omit [Finite J] in
private theorem centerTransfer_conjugate (e : A ≃* L) (l : A) (z : coreCenter A) :
    ((centerTransfer e (centerConjugate A l z)).val : L) =
      e l * ((centerTransfer e z).val : L) * (e l)⁻¹ := by
  rw [centerTransfer_val,centerTransfer_val,←map_inv,←map_mul,←map_mul]
  apply congrArg e
  apply Subtype.ext
  change (((BinaryCoverCoordinates.centerEquiv.symm (centerConjugate A l z)).val : A) : G) =
    (l : G) * (((BinaryCoverCoordinates.centerEquiv.symm z).val : A) : G) * (l : G)⁻¹
  rw [BinaryCoverCoordinates.centerEquiv_symm_val,BinaryCoverCoordinates.centerEquiv_symm_val]
  rfl

private noncomputable def coefficients (e : A ≃* L) : coreCenter A →* Multiplicative (Fin 3 → ZMod 2) :=
  (t.largeCenterProjection common earlier).comp (centerTransfer e).toMonoidHom

private theorem coefficients_kernel (e : A ≃* L) :
    (coefficients t common earlier e).ker = centerKernel A := by
  ext z
  change t.largeCenterProjection common earlier (centerTransfer e z) = 1 ↔
    (z : G) ∈ centralizer (A : Set G)
  rw [t.largeCenterProjection_eq_one_iff common earlier]
  constructor
  · intro hz l hl
    have he := mem_center_iff.mp hz (e ⟨l,hl⟩)
    rw [centerTransfer_val,←map_mul,←map_mul] at he
    have hh := congrArg Subtype.val (e.injective he)
    change l * (((BinaryCoverCoordinates.centerEquiv.symm z).val : A) : G) =
      (((BinaryCoverCoordinates.centerEquiv.symm z).val : A) : G) * l at hh
    simpa only [BinaryCoverCoordinates.centerEquiv_symm_val] using hh
  · intro hz
    apply mem_center_iff.mpr
    intro l
    obtain ⟨l,rfl⟩ := e.surjective l
    rw [centerTransfer_val,←map_mul,←map_mul]
    apply congrArg e
    apply Subtype.ext
    change (l : G) * (((BinaryCoverCoordinates.centerEquiv.symm z).val : A) : G) =
      (((BinaryCoverCoordinates.centerEquiv.symm z).val : A) : G) * (l : G)
    rw [BinaryCoverCoordinates.centerEquiv_symm_val]
    exact hz l l.property

/-- The literal natural quotient of the full core center, with its complete
component-central kernel, transported through the given component inclusion. -/
noncomputable def model (e : A ≃* L) : CenterModel A CentralCover.LinearThree.natural where
  quotientIso := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (h.quotientEquiv.trans common.natural.marking)
  moduleIso := (QuotientGroup.quotientMulEquivOfEq (coefficients_kernel t common earlier e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (coefficients t common earlier e)
      ((t.largeCenterProjection_surjective common earlier).comp (centerTransfer e).surjective))
  intertwining l z := by
    apply Multiplicative.toAdd.injective
    exact t.largeCenterProjection_action common earlier (e l) (centerTransfer e z)
      (centerTransfer e (centerConjugate A l z)) (centerTransfer_conjugate e l z)
  core_centralizes := by
    rintro _ ⟨l,hl,rfl⟩ z hz
    let zC : coreCenter A := ⟨z,hz⟩
    have hl' : e l ∈ pCore 2 L := by
      rw [←pCore_map_iso 2 e]
      exact mem_map_of_mem _ hl
    have he := t.large_core_centralizes_center common earlier (e l) hl' (centerTransfer e zC)
    rw [centerTransfer_val,←map_inv,←map_mul,←map_mul] at he
    have hh := congrArg Subtype.val (e.injective he)
    change (l : G) * (((BinaryCoverCoordinates.centerEquiv.symm zC).val : A) : G) * (l : G)⁻¹ =
      (((BinaryCoverCoordinates.centerEquiv.symm zC).val : A) : G) at hh
    rw [BinaryCoverCoordinates.centerEquiv_symm_val] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryLargeCenter

open Subgroup Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryLargeCenter
open RankOneConfiguration EightGeometry.NaturalModule.Recognition SmallExtension
  SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree ChapterC
namespace SourceConsumer
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass} {d : LocalData G}
  {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)
include s
/-- The source plane and its marked parabolic supply all coefficient actors;
only the literal action on the whole commutator core remains explicit. -/
theorem false_of_centerModel_and_core_centralizing
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : CenterModel c.L natural)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) : False := by
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

  let B := (d.Yplus.subgroupOf c.L).map m.actorMap
  have ht' : planeTransvection ∈ B.map (MulAut.conj a).toMonoidHom := by
    simpa only [B,map_map] using ht
  have hr' : planeRotation ∈ B.map (MulAut.conj a).toMonoidHom := by
    simpa only [B,map_map] using hr
  have hnat : DetectedOn natural B := by
    apply detectedOn_transport natural natural (MulAut.conj a)
      (LinearEquiv.ofBijective (natural a) (natural.apply_bijective a)) _ B
      (detectedOn_of_marked_matrices _ ht' hr')
    intro b v
    change natural a (natural b v) = natural (a * b * a⁻¹) (natural a v)
    rw [map_mul,map_mul]
    simp only [Module.End.mul_apply,inv_self_apply]
  let : (actionKernel I c.L).Normal := actionKernel_normal
    ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal)
  have hzero := centralizerImage_eq_bot_of_detected_model d c s.contains s.normal m
    (specialLinearNatural_injective 3) hDQ hnat
  have hDL := (plusImage_eq_bot_iff inf_le_left).mp hzero
  obtain ⟨hVI,hVY,hN⟩ := s.first_plane_control
  apply c.outside
  exact (le_centralizer_iff.mp ((le_inf hVI hVY).trans hDL)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)

end SourceConsumer
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryLargeCenter

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open Theory.GroupTheory RankOneConfiguration EightGeometry.NaturalModule.Recognition
  SmallExtension SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree ChapterC
open BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The original large-distance setup supplies the natural coefficient model
on the actual center quotient, retaining its component-central kernel. -/
noncomputable def source_binary_large_centerModel
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    CenterModel c.L natural :=
  BinaryLargeCenter.model t common earlier (subgroupOfEquivOfLe (component_le c)).symm

/-- The literal original source31 application discharges the center model and
marked coefficient actors. The remaining action is C_I(Yplus) on the whole
commutator core, not the action of the original two-core on the fixed factor. -/
theorem source_binary_large_false_of_core_centralizing
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) : False := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := (e.trans Matrix.PSL3Two.equiv).isSimpleGroup
  exact BinaryLargeCenter.SourceConsumer.false_of_centerModel_and_core_centralizing s hm
    (source_binary_large_centerModel s e t common earlier) hDQ

/-- Prescribed replacement now feeds the direct coefficient route at the
original source pair; no original fixed-four-group centrality is assumed. -/
theorem source_binary_large_false_of_replacement_and_core_centralizing
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (replacement : ∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) : False :=
  source_binary_large_false_of_core_centralizing s hm e t common
    (Source44.SourceEarlier.earlier common hb replacement) hDQ

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
