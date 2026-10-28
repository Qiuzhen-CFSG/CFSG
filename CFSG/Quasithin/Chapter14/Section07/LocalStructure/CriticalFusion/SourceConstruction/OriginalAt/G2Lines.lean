module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceSeedLines
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.G2Incidence

/-!
# The reciprocal G₂ line family at the original G,T

The critical offender constructs both compatible natural/Weyl markings.
The identical commutator family gives actual conjugates of V over both
original central points, in the same ambient group.

Only Structural1222At at the original G,T is used. The source producers
qt-d-1222-source and qt-d-1434-source retain the earlier structural and
faithful inputs. Original residual alternatives, uniqueness, relative
component and alternating recognition retain qt-d-14763-source-data.
Final source 14.7.75 discharge remains with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.53–63, pp.1065–1069; F.9.18, pp.325–326.
The reused concrete model calculations retain LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

include c in
theorem source_reciprocal_geometry_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) :
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Bijective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
    ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      (∀ a v, E (m.action (i a) v) = σ a (E v)) ∧
    ∃ (p : Atlas.G2.SingularPoints (ZMod 2)) (r : SourceReversal.Geometry path)
      (q : Atlas.G2.SingularPoints (ZMod 2)),
      (star F path.Uα).map i = fullCentralizer m.singularMap m.action p ∧
      r.path.RankSelection ∧ r.path.Uα ≤ F.Ri L 1 ∧
      (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q ∧
      (¬ F.Vi 1 ≤ path.Uα) ∧ (¬ F.Vi 1 ≤ r.path.Uα) ∧
      ({C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
        C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
        C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}) ∧
      ∀ C : Subgroup G, C ≠ ⊥ →
        (∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα, C = ⁅F.U,zpowers b⁆) →
        Nat.card C = 4 ∧ C ≤ F.U ∧ C ≤ path.Uα ∧
          (∃ a : F.H, C ⊔ F.Vi 1 = conjugate V a) ∧
          (∃ g : G, C ⊔ path.Zα = conjugate V g) := by
  obtain ⟨i,hi,hJ,m,E,he,hrest⟩ := source_recognized_reciprocal_family_at
    c h hab hcomponent hfit eK structural hf hcomm P hP orbit path hplace selection
    (source_critical_point_not_le_span_at c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection)
  have hs := G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.source_full_actor_of_ff
    σ m.action i hi E.symm
    (fun a v => by rw [←E.apply_symm_apply v,←he,E.symm_apply_apply,E.symm_apply_apply]) hJ
    Atlas.G2.Natural.BinaryModelOffenders.rank_le_two
    (fun A hA hr => by have hh := model_small_rank_bound m A hA (by omega); omega)
    (fun A _ hA hr => by have hh := model_small_rank_bound m A hA (by omega); omega)
    ⟨star F path.Uα,source_critical_offender_at c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection⟩
  obtain ⟨p,r,q,hA,hrs,hrplace,hrA,hpoint,hrpoint,hfamily⟩ := hrest
  refine ⟨i,⟨hi,hs.1⟩,hJ,m,E,he,p,r,q,hA,hrs,hrplace,hrA,hpoint,hrpoint,hfamily,?_⟩
  intro C hC hCb
  have hreverse : C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
      C = conjugate ⁅F.U,zpowers b⁆ r.conjugator := by
    change C ∈ {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
      C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}
    rw [←hfamily]
    exact ⟨hC,hCb⟩
  obtain ⟨_,b',hb',hCe⟩ := hreverse
  have hn' : ⁅F.U,zpowers b'⁆ ≠ ⊥ := by
    intro hz
    apply hC
    rw [hCe,hz]
    exact map_bot _
  obtain ⟨a,ha⟩ := source_commutator_seed_conjugate c h r.path hrplace i ⟨hi,hs.1⟩
    m E he q hrA hrpoint b' hb' hn'
  have hsecond : ∃ g : G, C ⊔ path.Zα = conjugate V g := by
    refine ⟨(a:G)*r.conjugator,?_⟩
    have hh := congrArg (fun D : Subgroup G => conjugate D r.conjugator) ha
    change (⁅F.U,zpowers b'⁆ ⊔ F.Vi 1).map _ = _ at hh
    rw [Subgroup.map_sup] at hh
    change conjugate ⁅F.U,zpowers b'⁆ r.conjugator ⊔
      conjugate (F.Vi 1) r.conjugator = _ at hh
    rw [r.base_point,←hCe] at hh
    refine hh.trans ?_
    change (V.conjBy (a:G)⁻¹).conjBy r.conjugator⁻¹ = V.conjBy ((a:G)*r.conjugator)⁻¹
    rw [←conjBy_mul,mul_inv_rev]
  obtain ⟨b,hb,rfl⟩ := hCb
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hθ : (path.Uα.subgroupOf F.H).map (i.comp (starMap F)) =
      fullCentralizer m.singularMap m.action p := by rw [←map_map]; exact hA
  obtain ⟨_,_,_,hc⟩ := source_commutator_line c h path hplace m E
    (i.comp (starMap F)) (fun a v => he (starMap F a) v) p
    (derivedActorLift (i.comp (starMap F)) path.Uα) (derivedActorLift_le _ _) hpoint
    (derivedActorLift_image _ m p _ hθ) b hb hC
  have hbA := zpowers_le.mpr (derivedActorLift_le _ _ hb)
  exact ⟨hc,le_normalizer_iff_commutator_le_left.mp ((hbA.trans hAH).trans c.normalized),
    (commutator_mono le_rfl hbA).trans
      (le_normalizer_iff_commutator_le_right.mp (normalizes_partner h path)),
    source_commutator_seed_conjugate c h path hplace i ⟨hi,hs.1⟩ m E he p hA hpoint b hb hC,
    hsecond⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
