module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.AbelianGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses.AutomorphismFixers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.Actor
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.G2.QuotientPlane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.Linear

/-!
# Binary coefficient quotients in the original small branch

A marked realization of Z(Q)/C_Z(Q)(L) suffices for the central-cover
argument: the central kernel need not vanish. Two explicit elements of
the actual Y₊ image have trivial automorphism fixer in SL₃(2). The simple
star component is self-centralizing, so they kill the full star centralizer.
The original conjugate-generation theorem then makes C_I(Y₊) centralize
an abelian Q, and the checked cocycle detection gives the contradiction.

Source: Aschbacher–Smith15.3.31, printed p.1132.
-/
public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover CentralCover.LinearThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass} {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
  {ρ : Representation (ZMod 2) SL V}

private def recoordinateCoefficients {L : Subgroup G} (m : CenterModel L ρ) (a : SL) :
    CenterModel L ρ where
  quotientIso := m.quotientIso.trans (MulAut.conj a)
  moduleIso := m.moduleIso.trans (LinearModels.FullCenter.actionEquiv (ρ := ρ) a)
  intertwining l z := by
    change Multiplicative.ofAdd (ρ a (m.coordinates (centerConjugate L l z)).toAdd) = _
    rw [m.coordinates_conjugate]
    apply congrArg Multiplicative.ofAdd
    change ρ a (ρ (m.actorMap l) (m.coordinates z).toAdd) =
      ρ (a * m.actorMap l * a⁻¹) (ρ a (m.coordinates z).toAdd)
    rw [map_mul,map_mul]
    simp only [Module.End.mul_apply,inv_self_apply]
  core_centralizes := m.core_centralizes

/-- Every natural plane has the marked parabolic's order, independently of
the chosen coefficient coordinates. -/
theorem natural_plane_stabilizer_card (W : Submodule (ZMod 2) Space)
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

open Representation.BinaryOffender CentralCover.LinearModels MarkedMS.Constituents
  MarkedModelAssembly
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {L E : Subgroup G}

private noncomputable def markedPlane_of_embedding (m : FullCenter L ρ)
    (hE : E ≤ coreCenter L) (W : Submodule (ZMod 2) Space)
    (hd : Module.finrank (ZMod 2) W = 2)
    (f : Space →ₗ[ZMod 2] V) (hf : Function.Injective f)
    (he : ∀ a v, f (natural a v) = ρ a (f v))
    (hm : W.map f = centerPlane m E) : MarkedPlane m E where
  space := W
  dimension := hd
  embedding := f
  injective := hf
  equivariant := he
  contained := hE
  membership z := by
    rw [← coord_mem_centerPlane m E z, ← hm]
    constructor
    · rintro ⟨v, hv, heq⟩
      exact ⟨v, hv, (congrArg Multiplicative.ofAdd heq).symm⟩
    · rintro ⟨v, hv, heq⟩
      exact ⟨v, hv, (congrArg Multiplicative.toAdd heq).symm⟩

private def pairCoordinates : (Space × Space) ≃ₗ[ZMod 2] (Fin 2 → Space) where
  toFun v := ![v.1, v.2]
  invFun v := (v 0, v 1)
  left_inv _ := rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

private theorem pairCoordinates_action (a : SL) (v : Space × Space) :
    pairCoordinates ((natural.prod natural) a v) =
      repeated binaryNatural 2 a (pairCoordinates v) := by
  ext i j
  fin_cases i <;> rfl

private noncomputable def piCenter (m : FullCenter L (natural.prod natural)) :
    FullCenter L (repeated binaryNatural 2) where
  quotientIso := m.quotientIso
  equiv := m.equiv.trans pairCoordinates.toAddEquiv.toMultiplicative
  action l z := by
    change Multiplicative.ofAdd (pairCoordinates (m.equiv (centerConjugate L l z)).toAdd) = _
    rw [m.action]
    exact congrArg Multiplicative.ofAdd (pairCoordinates_action _ _)

omit [Finite G] in
private theorem mem_piCenter_plane (m : FullCenter L (natural.prod natural))
    (E : Subgroup G) (v : Fin 2 → Space) :
    v ∈ centerPlane (piCenter m) E ↔ pairCoordinates.symm v ∈ centerPlane m E := Iff.rfl

private noncomputable def doubledMarkedPlane (m : FullCenter L (natural.prod natural))
    (hE : E ≤ coreCenter L) (hcard : Nat.card E = 4)
    (P : Subgroup G) (hP : Nat.card ((P.subgroupOf L).map m.actor) = 24)
    (hn : P = L ⊓ normalizer (E : Set G))
    (hd : Disjoint (centerPlane (piCenter m) E)
      (fixedSpace (repeated binaryNatural 2) ((P.subgroupOf L).map m.actor))) :
    MarkedPlane m E := by
  have hs : ((P.subgroupOf L).map (piCenter m).actor) =
      subspaceStabilizer (repeated binaryNatural 2) (centerPlane (piCenter m) E) := by
    rw [hn, inf_subgroupOf_left]
    exact centerPlane_stabilizer (piCenter m) E hE
  let b := Classical.choice (BinaryGeometry.exists_binaryDoubledLine
    (centerPlane (piCenter m) E) ((P.subgroupOf L).map m.actor)
    ((centerPlane_card _ hE).trans hcard) hP hs.le hd)
  refine markedPlane_of_embedding m hE b.plane (plane_dimension _ b.plane_card)
    (pairCoordinates.symm.toLinearMap.comp b.embedding)
    (pairCoordinates.symm.injective.comp b.injective) ?_ ?_
  · intro a v
    apply pairCoordinates.injective
    change pairCoordinates (pairCoordinates.symm (b.embedding (natural a v))) =
      pairCoordinates ((natural.prod natural) a (pairCoordinates.symm (b.embedding v)))
    rw [LinearEquiv.apply_symm_apply, pairCoordinates_action,
      LinearEquiv.apply_symm_apply]
    exact b.equivariant a v
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hmem : b.embedding w ∈ centerPlane (piCenter m) E := b.image.le ⟨w, hw, rfl⟩
      exact (mem_piCenter_plane m E _).mp hmem
    · intro hv
      have hh : pairCoordinates v ∈ b.plane.map b.embedding := by
        rw [b.image]
        apply (mem_piCenter_plane m E _).mpr
        rwa [pairCoordinates.symm_apply_apply]
      obtain ⟨w, hw, he⟩ := hh
      exact ⟨w, hw, (congrArg pairCoordinates.symm he).trans
        (pairCoordinates.symm_apply_apply v)⟩

namespace SourceData
variable (s : SourceData κ d c)
include s

/-- Marked coefficient actors kill the centralizer in the literal full star
quotient, independently of a whole-center splitting. -/
theorem binary_star_centralizer_of_coefficients
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (m : CenterModel c.L ρ)
    (ht : planeTransvection ∈ (d.Yplus.subgroupOf c.L).map m.actorMap)
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.actorMap) :
    centralizer (d.starImage I d.Yplus : Set (d.Star I)) = ⊥ := by
  let K := d.starImage I c.L
  let := EightGeometry.NaturalModule.Recognition.starComponent_normal d c s.normal
  let q := coreQuotientEquivStar d c s.normal s.sylow s.sylow_eq
  let e : K ≃* SL := q.symm.trans m.quotientIso
  let : IsSimpleGroup K := q.symm.isSimpleGroup
  have hcomm : ¬ IsMulCommutative K := by
    intro hc
    let := hc
    let : IsQuasisimple K := c.star_quasisimple
    exact Group.IsPerfect.not_isSolvable K
      (Group.isSolvable_of_comm (isMulCommutative_iff.mp hc))
  have hself : centralizer (K : Set (d.Star I)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient K hcomm
      (MarkedMS.Constituents.SourceReduction.star_component_two_quotient d c s.normal
        s.generated s.sylow s.sylow_eq)
      (d.star_twoCore_eq_bot ⟨s.sylow,s.sylow_eq⟩
        (d.Z_le_S (d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le))))
  let a : d.Star I →* MulAut SL :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have ha : Function.Injective a := (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hself)
  have hmark (l : c.L) : m.actorMap l = e (componentMap d c l) := by
    change m.quotientIso (QuotientGroup.mk' (pCore 2 c.L) l) =
      m.quotientIso (q.symm (componentMap d c l))
    rw [← coreQuotientEquivStar_apply d c s.normal s.sylow s.sylow_eq]
    exact congrArg m.quotientIso (q.symm_apply_apply _).symm
  apply _root_.eq_bot_iff.mpr
  intro x hx
  have hfix : ∀ b ∈ (d.Yplus.subgroupOf c.L).map m.actorMap, a x b = b := by
    rintro b ⟨l,hl,rfl⟩
    rw [hmark]
    change e (MulAut.conjNormal x (e.symm (e (componentMap d c l)))) = _
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    have hcomm := mem_centralizer_iff.mp hx
      (d.starMap I ⟨l, component_le c l.property⟩)
      (show d.starMap I ⟨l, component_le c l.property⟩ ∈ d.starImage I d.Yplus from
        mem_map_of_mem _ hl)
    change x * d.starMap I ⟨l, component_le c l.property⟩ * x⁻¹ = _
    rw [←hcomm,mul_inv_cancel_right]
    rfl
  have hx1 : a x = 1 := automorphism_eq_one_of_fixed_marked_matrices
    (a x) (hfix _ ht) (hfix _ hr)
  exact mem_bot.mpr (ha (hx1.trans a.map_one.symm))

/-- Actual source31 contradiction from a marked natural coefficient quotient,
allowing its original nontrivial central kernel. -/
theorem binary_abelian_false_of_coefficients
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (m : CenterModel c.L ρ) (hfaith : Function.Injective ρ)
    (hQ : IsMulCommutative (extensionCore c.L))
    (ht : planeTransvection ∈ (d.Yplus.subgroupOf c.L).map m.actorMap)
    (hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map m.actorMap)
    (hdet : DetectedOn ρ ((d.Yplus.subgroupOf c.L).map m.actorMap)) : False := by
  have hstar := s.binary_star_centralizer_of_coefficients m ht hr
  have hDQ := s.centralizes_abelian_core hstar hQ
  let : (actionKernel I c.L).Normal := actionKernel_normal
    ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal)
  have hzero := centralizerImage_eq_bot_of_detected_model d c s.contains s.normal m hfaith hDQ hdet
  have hDL := (plusImage_eq_bot_iff inf_le_left).mp hzero
  obtain ⟨hVI,hVY,hN⟩ := s.first_plane_control
  apply c.outside
  exact (le_centralizer_iff.mp ((le_inf hVI hVY).trans hDL)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)

omit [Finite G] in
/-- The actual component parabolic has order 24 in any coefficient
marking of its binary linear-three quotient. -/
theorem binary_centerModel_parabolic_card
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L) (m : CenterModel c.L ρ) :
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

/-- The original four-group and small-parabolic marking produce all coefficient
actors needed to exclude an abelian core with one natural coefficient quotient. -/
theorem binary_natural_abelian_false
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : CenterModel c.L natural)
    (hQ : IsMulCommutative (extensionCore c.L)) : False := by
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
  exact s.binary_abelian_false_of_coefficients (recoordinateCoefficients m a)
    (specialLinearNatural_injective 3) hQ ht hr (detectedOn_of_marked_matrices _ ht hr)

/-- The actual short-block output of the binary MS theorem supplies the
coefficient model used above, including any component-fixed central kernel. -/
theorem binary_natural_short_false
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (hs : ChapterC.IsShort c.L)
    (m : ChapterC.BlockModuleModel c.L (BlockModels.multiplicativeAction natural)) : False := by
  have hQ : IsElementaryAbelian 2 (extensionCore c.L) := by
    rw [← BlockModels.blockU_map]
    let := hs.elementary
    exact IsElementaryAbelian.map_subtype
  let := hQ
  exact s.binary_natural_abelian_false hm (BlockModels.centerModel hs natural m) inferInstance

/-- The doubled natural core is excluded using just the original source
parabolic; no classification record for the other MS rows is required. -/
theorem binary_double_abelian_false
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : AbelianCore c.L (natural.prod natural)) : False := by
  have hfixed (v : Space × Space)
      (hv : ∀ a : SL, (natural.prod natural) a v = v) : v = 0 := by
    apply Prod.ext
    · exact fixed_marked_matrices_eq_zero v.1
        (congrArg Prod.fst (hv _)) (congrArg Prod.fst (hv _))
    · exact fixed_marked_matrices_eq_zero v.2
        (congrArg Prod.snd (hv _)) (congrArg Prod.snd (hv _))
  have hcard : Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map m.fullCenter.actor) = 24 :=
    s.binary_centerModel_parabolic_card hm (m.fullCenter.model hfixed)
  have hdis : Disjoint (centerPlane (piCenter m.fullCenter) d.V₂)
      (fixedSpace (repeated binaryNatural 2)
        (((d.M ⊓ c.L).subgroupOf c.L).map m.fullCenter.actor)) := by
    apply centerPlane_fixed_disjoint (piCenter m.fullCenter) d.V₂ d.Yplus (d.M ⊓ c.L)
    · exact s.component_residual ▸ map_subtype_le _
    · exact s.contains
    · exact s.line.plane_fixed_trivial d
  let p := doubledMarkedPlane m.fullCenter s.plane_le_coreCenter
    (d.action.card_plane _) (d.M ⊓ c.L) hcard s.component_parabolic hdis
  exact NaturalCoreModels.SourceWitnesses.excluded_two s m p

end SourceData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
