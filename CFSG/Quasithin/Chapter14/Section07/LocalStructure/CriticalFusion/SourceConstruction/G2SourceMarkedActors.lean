module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceModels
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceNoncontainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceModelFamilies

/-!
# Full pencil actors, point noncontainment and the common source family

For either recognized G₂ module the full pencil centralizer is an elementary
eight of fixed codimension three, and its fixed space is contained in its
moved space. On the original critical pair, mutual normalization and
abelianness put [U,Uα] inside U ∩ Uα and make that intersection fixed.
The two model spaces therefore sandwich its image, proving the intersection
image and index in 14.7.61(2),(4).

The actual dual-section obstruction now proves V₁ is not contained in Uα.
The final application feeds this result into G2SourceModelFamilies, so neither
point noncontainment nor a common-family identity is assumed there. Both
indexing groups are constructed on the original action and quotient marking.

This is conditional on identifying the SAME critical actor Uα* with the
full model pencil centralizer. The 14.7.60–61 proof of that identification,
its reciprocal counterpart, Zα not contained in U, and the endpoint line
families remain obligations of this G₂ source branch. The earlier full
core-commutator identity and the faithful/component inputs retain their
final discharge with qt-d-14775-source.

Source: Aschbacher–Smith, 14.7.55(4),(8), 14.7.61–62 and formula (d),
printed pp.1066–1069. The concrete octonion models and root calculations
retain the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open G2Exclusion G2Exclusion.MarkedGeometry G2Exclusion.MarkedGeometry.MarkedPencil
open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Atlas.G2
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

private theorem model_equivariant (m : BinaryG2Module) : m.singularMap.Equivariant m.action := by
  cases m with
  | natural => exact naturalMap_equivariant
  | weyl => exact weylMap_equivariant

/-- The actual full pencil centralizer is a best offender on either recognized module. -/
theorem model_fullCentralizer_bestOffender (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) :
    IsBestOffender m.action (fullCentralizer m.singularMap m.action p) := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • Atlas.G2.firstPoint = p := by rw [← hg,inv_smul_smul]
  apply (model_bestOffender m _).mpr
  refine ⟨g⁻¹,?_⟩
  rw [← fullCentralizer_firstPoint m.singularMap m.action (model_equivariant m),
    fullCentralizer_conjugate m.singularMap m.action (model_equivariant m),hp]

/-- The same full pencil actor has fixed codimension three in both models. -/
theorem model_fullCentralizer_fixedCodim (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) :
    fixedCodim m.action (fullCentralizer m.singularMap m.action p) = 3 := by
  have hb := model_fullCentralizer_bestOffender m p
  cases m with
  | natural =>
    change IsBestOffender (Atlas.G2.Natural.action (ZMod 2))
      (fullCentralizer naturalMap (Atlas.G2.Natural.action (ZMod 2)) p) at hb
    change fixedCodim (Atlas.G2.Natural.action (ZMod 2))
      (fullCentralizer naturalMap (Atlas.G2.Natural.action (ZMod 2)) p) = 3
    exact Atlas.G2.NaturalOffenders.natural_offender_fixedCodim
      (n := 1) (by norm_num) (by decide) _ (hb.isOffender _)
  | weyl =>
    change IsBestOffender (Atlas.G2.Natural.traceZeroAction (ZMod 2))
      (fullCentralizer weylMap (Atlas.G2.Natural.traceZeroAction (ZMod 2)) p) at hb
    change fixedCodim (Atlas.G2.Natural.traceZeroAction (ZMod 2))
      (fullCentralizer weylMap (Atlas.G2.Natural.traceZeroAction (ZMod 2)) p) = 3
    rw [Atlas.G2.Natural.BinaryModelOffenders.weyl_fixedCodim]
    have hb' := (Atlas.G2.Natural.BinaryModelOffenders.weyl_bestOffender_iff_natural _).mp hb
    exact Atlas.G2.NaturalOffenders.natural_offender_fixedCodim
      (n := 1) (by norm_num) (by decide) _ (hb'.isOffender _)

/-- Fixed vectors of the full pencil actor lie in its moved space. -/
theorem model_fullCentralizer_fixed_le_moved (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) :
    fixedSpace m.action (fullCentralizer m.singularMap m.action p) ≤
      subspaceCommutator m.action ⊤ (fullCentralizer m.singularMap m.action p) := by
  obtain ⟨a,ha,hd⟩ := SetLike.not_le_iff_exists.mp
    (fullCentralizer_not_le_derived m.singularMap m.action (model_equivariant m) p)
  have hout : a ∉ derivedCentralizer m.singularMap m.action p := fun hh => hd hh.2
  have he : fixedSpace m.action (derivedCentralizer m.singularMap m.action p) =
      subspaceCommutator m.action ⊤ (fullCentralizer m.singularMap m.action p) := by
    cases m with
    | natural => exact (natural_full_spaces p a ha hout).2.2
    | weyl => exact (weyl_full_spaces p a ha hout).2.2
  rw [← he]
  intro v hv a
  exact hv ⟨a,a.property.1⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

/-- Mutual normalization sandwiches the original intersection between moved and fixed spaces. -/
theorem source_marked_intersection_image
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) (path : CriticalPath (L := L) F)
    (hAH : path.Uα ≤ F.H)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    c.imageSpace (F.U ⊓ path.Uα) = fixedSpace σ (star F path.Uα) := by
  let := hab
  let : IsMulCommutative path.Uα :=
    inferInstanceAs (IsMulCommutative (F.U.map (MulAut.conj path.conjugator⁻¹).toMonoidHom))
  have hfix : (fixedSpace m.action (fullCentralizer m.singularMap m.action p)).map E.toLinearMap =
      fixedSpace σ (star F path.Uα) := by
    have hh := fixedSpace_map_equivariant σ m.action i E.symm
      (fun a v => by rw [← E.apply_symm_apply v,← he,E.symm_apply_apply,E.symm_apply_apply])
      (star F path.Uα)
    rw [hA] at hh
    exact (Submodule.map_symm_eq_iff E).mp hh
  have hmoved : (subspaceCommutator m.action ⊤ (fullCentralizer m.singularMap m.action p)).map
      E.toLinearMap = c.imageSpace ⁅F.U,path.Uα⁆ := by
    have hh := subspaceCommutator_map_embedding (σ.comp (starMap F)) m.action
      (i.comp (starMap F)) E.toLinearMap
      (fun a v => (he (starMap F a) v).symm) (path.Uα.subgroupOf F.H) ⊤
    rw [Submodule.map_top,LinearEquiv.range,← Subgroup.map_map] at hh
    change subspaceCommutator (σ.comp (starMap F)) ⊤ (path.Uα.subgroupOf F.H) =
      (subspaceCommutator m.action ⊤ ((star F path.Uα).map i)).map E.toLinearMap at hh
    rw [hA] at hh
    rw [commutator_comm,c.imageSpace_commutator _ _ hAH le_rfl,imageSpace_U c]
    exact hh.symm
  have hcomm : ⁅F.U,path.Uα⁆ ≤ F.U ⊓ path.Uα :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (hAH.trans c.normalized))
      (le_normalizer_iff_commutator_le_right.mp (normalizes_partner h path))
  apply le_antisymm
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff _ _).mp hv
    rintro ⟨_,a,ha,rfl⟩
    change (σ.comp (starMap F)) a (c.coordinates u).toAdd = _
    rw [← c.equivariant]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr
      ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative path.Uα)) ha (u : G) hu.2).symm
  · rw [← hfix]
    exact ((Submodule.map_mono (model_fullCentralizer_fixed_le_moved m p)).trans_eq hmoved).trans
      (c.imageSpace_mono hcomm)

include c in
/-- The original intersection quotient and the same star actor both have order eight. -/
theorem source_marked_intersection_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) (path : CriticalPath (L := L) F)
    (hAH : path.Uα ≤ F.H)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    ((F.U ⊓ path.Uα) ⊔ F.Vi 1).relIndex F.U = Nat.card (star F path.Uα) := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hcard : Nat.card (star F path.Uα) = 8 := by
    rw [← card_map_of_injective (K := star F path.Uα) hi,hA]
    exact (fullCentralizer_structure m.singularMap m.action (model_equivariant m) p).2
  have hcod : fixedCodim σ (star F path.Uα) = 3 := by
    have hh := fixedCodim_map_equivariant σ m.action i E.symm
      (fun a v => by rw [← E.apply_symm_apply v,← he,E.symm_apply_apply,E.symm_apply_apply])
      (star F path.Uα)
    rw [hA,model_fullCentralizer_fixedCodim] at hh
    exact hh
  let B := (F.U ⊓ path.Uα) ⊔ F.Vi 1
  let D := (B.subgroupOf F.U).map c.coordinates
  have hD : Nat.card D = 2 ^ Module.finrank (ZMod 2) (fixedSpace σ (star F path.Uα)) := by
    change Nat.card (c.imageSpace B) = _
    rw [imageSpace_sup_point c _ inf_le_left,
      source_marked_intersection_image c h hab path hAH m E i he p hA,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hidx : D.index = B.relIndex F.U :=
    index_map_eq _ c.onto (by rw [c.kernel_eq]; exact comap_mono le_sup_right)
  have hc := D.card_mul_index
  have hW : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).trans (by rw [Nat.card_zmod])
  rw [hD,hW,← fixedCodim_add_finrank σ (star F path.Uα),hcod,add_comm,pow_add] at hc
  rw [hcard]
  exact hidx.symm.trans (Nat.eq_of_mul_eq_mul_left (by positivity) hc)

include c in
/-- The full critical-actor marking supplies the index needed by the source duality contradiction. -/
theorem source_marked_point_noncontainment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    ¬ F.Vi 1 ≤ path.Uα := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  exact source_point_noncontainment c h hab hcomponent hfit eK hf hcomm path hplace selection
    (source_marked_intersection_index c h hab path hAH m E i hi he p hA)

/-- Construct both original indexing subgroups and their common nontrivial
commutator family, discharging point noncontainment by the source duality argument. -/
theorem source_common_family_of_full_critical_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    let B := derivedActorLift (i.comp (starMap F)) path.Uα
    let R := polarLift c m E p
    (¬ F.Vi 1 ≤ path.Uα) ∧
    ({C | C ≠ ⊥ ∧ ∃ b ∈ B, C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ w ∈ R, C = ⁅path.Uα,zpowers w⁆}) ∧
    (∀ b ∈ B, path.Uα ⊓ (⁅F.U,zpowers b⁆ ⊔ F.Vi 1) = ⁅F.U,zpowers b⁆) ∧
    fixedSpace (σ.comp (starMap F)) (path.Uα.subgroupOf F.H) =
      c.imageSpace (F.U ⊓ centralizer (path.Uα : Set G)) := by
  have hpoint := source_marked_point_noncontainment c h hab hcomponent hfit eK hf hcomm
    path hplace selection m E i hi he p hA
  exact ⟨hpoint,source_common_family_of_critical_marking c h path hplace m E i
    (fun a v => he (starMap F a) v) p hpoint hA⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
