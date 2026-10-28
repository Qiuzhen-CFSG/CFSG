module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceReciprocity
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Selection

/-!
# The reciprocal G₂ actor at the original G,T

The full actor determines the actual reciprocal path and its two rank
identities. Transport the common commutator family through the unchanged
quotient maps and retain the original point markings.

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
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

include c in
theorem source_full_actor_reciprocity_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    (¬ F.Vi 1 ≤ path.Uα) ∧ (¬ path.Zα ≤ F.U) ∧
    ∃ r : SourceReversal.Geometry path, r.path.RankSelection ∧
      r.path.Uα ≤ F.Ri L 1 ∧
      (F.U ⊓ r.path.Qα).relIndex F.U = 8 ∧ Nat.card (star F r.path.Uα) = 8 ∧
      ∃ q : Atlas.G2.SingularPoints (ZMod 2),
        (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  obtain ⟨hD,hidx,hcard⟩ := source_full_actor_core_and_orders c h hab path hAH m E i hi he p hA
  have hpoint := source_marked_point_noncontainment c h hab hcomponent hfit eK hf hcomm
    path hplace selection m E i hi he p hA
  obtain ⟨r⟩ := LocalReduction.exists_reversal_of_star_ne_bot_at h structural path hAH
    (path.star_ne_bot selection)
  have hrplace := LocalReduction.critical_le_Ri_at h structural r.path
  have hrH : r.path.Uα ≤ F.H := hrplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hridx : (F.U ⊓ r.path.Qα).relIndex F.U = 8 :=
    (r.reverse_index_of_placement hAH).trans hcard
  have hrcard : Nat.card (star F r.path.Uα) = 8 :=
    (r.reverse_star_of_placement hrH).trans hidx
  have hrs : r.path.RankSelection := {
    positive := by rw [hridx]; decide
    comparison := by rw [hridx,hrcard] }
  have hrpoint : ¬ r.path.Zα ≤ F.U := by
    intro hh
    apply hpoint
    have hh' := map_mono (f := (MulAut.conj r.conjugator⁻¹).toMonoidHom) hh
    change conjugate r.path.Zα r.conjugator ≤ conjugate F.U r.conjugator at hh'
    rwa [r.tip_point,r.base_U] at hh'
  obtain ⟨q,hq⟩ := source_full_critical_actor_of_point_not_le c h hab r.path hrplace hrs hrpoint
    m E i hi he
  have hrnot := source_marked_point_noncontainment c h hab hcomponent hfit eK hf hcomm
    r.path hrplace hrs m E i hi he q hq
  refine ⟨hpoint,?_,r,hrs,hrplace,hridx,hrcard,q,hq⟩
  intro hh
  apply hrnot
  apply (map_le_map_iff_of_injective (f := (MulAut.conj r.conjugator⁻¹).toMonoidHom)
    (MulAut.conj r.conjugator⁻¹).injective).mp
  change conjugate (F.Vi 1) r.conjugator ≤ conjugate r.path.Uα r.conjugator
  rwa [r.base_point,r.tip_U]

include c in
theorem source_reciprocal_family_of_partner_point_not_le_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hZU : ¬ path.Zα ≤ F.U)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v)) :
    ∃ (p : Atlas.G2.SingularPoints (ZMod 2)) (r : SourceReversal.Geometry path)
      (q : Atlas.G2.SingularPoints (ZMod 2)),
      (star F path.Uα).map i = fullCentralizer m.singularMap m.action p ∧
      r.path.RankSelection ∧ r.path.Uα ≤ F.Ri L 1 ∧
      (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q ∧
      (¬ F.Vi 1 ≤ path.Uα) ∧ (¬ F.Vi 1 ≤ r.path.Uα) ∧
      ({C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
        C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
        C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}) := by
  obtain ⟨p,hA⟩ := source_full_critical_actor_of_point_not_le c h hab path hplace selection
    hZU m E i hi he
  obtain ⟨hpoint,_,r,hrs,hrplace,_,_,q,hAr⟩ :=
    source_full_actor_reciprocity_at c h hab hcomponent hfit eK structural hf hcomm
      path hplace selection m E i hi he p hA
  have hrpoint := source_marked_point_noncontainment c h hab hcomponent hfit eK hf hcomm
    r.path hrplace hrs m E i hi he q hAr
  exact ⟨p,r,q,hA,hrs,hrplace,hAr,hpoint,hrpoint,
    source_family_eq_reverse_family c h path hplace r hrplace m E i he p q hA hAr hpoint hrpoint⟩

include c in
theorem source_recognized_reciprocal_family_at
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
    (selection : path.RankSelection) (hZU : ¬ path.Zα ≤ F.U) :
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
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
        C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}) := by
  have hquad : IsQuadratic σ (star F path.Uα) := by
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ v
    exact LocalReduction.critical_quadratic h hab c path a ha b hb v
  have hbound : fixedCodim σ (star F path.Uα) ≤ 2 * rank (star F path.Uα) := by
    have hh := (source_critical_offender_of_point_not_le c h hab path hplace selection hZU).2
    omega
  obtain ⟨i,hi,hJ,hmodels⟩ := source_natural_or_weyl c h hab hcomponent hfit eK hf
    P hP orbit path hplace selection hquad hbound
  have hm : ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      ∀ a v, E (m.action (i a) v) = σ a (E v) := by
    rcases hmodels with ⟨E,he⟩ | ⟨E,he⟩
    · exact ⟨.natural,E,he⟩
    · exact ⟨.weyl,E,he⟩
  obtain ⟨m,E,he⟩ := hm
  exact ⟨i,hi,hJ,m,E,he,
    source_reciprocal_family_of_partner_point_not_le_at c h hab hcomponent hfit eK structural
      hf hcomm path hplace selection hZU m E i hi he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
