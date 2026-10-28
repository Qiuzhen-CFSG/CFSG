module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.Selection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# B.4.2 premises for the selected external FF constituent

Starting with the specified T-invariant Irr⁺ constituent and its genuine
FF action image, we construct the KT-action on the literal I/C_I(K).
The quotient projection is equivariant, and the action kernel is unchanged.
Consequently an offender descends with its rank preserved. Irreducibility
kills the two-core in the faithful image, so its entire generalized Fitting
subgroup is the quasisimple image of K. The component map, its central kernel,
and its quotient isomorphism are explicit.

Centerlessness of K, an earlier structural output in the external branch,
makes the remaining action kernel a two-group. The genuine SQTK hypothesis
therefore passes to this precise action image. Replacement supplies an actual
best offender, yielding the existing complete B42Hypotheses contract.

The source adapter retains the conjugation action on SeedAction.Space H V₃ V₁,
H = K L₁ T, the marked Sylow image, and the selected FF premise supplied by
SourceOrbit.Selection. Existence and selection of this constituent remain
with the parent source assembly. No B.4.2 classification, natural-module
identification, or tensor conclusion is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(3–4),
printed pp.325–326; B.4.2, pp.86–87; proof of 13.8.20(a), pp.954–955.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory CFSG.Quasithin
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
universe u
variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (P : Sylow 2 G) (I : Submodule (ZMod 2) V)
    (hIL : K ≤ subspaceStabilizer ρ I) (hIP : (P : Subgroup G) ≤ subspaceStabilizer ρ I)

/-- The actual subgroup K*T, with the source Sylow subgroup retained. -/
abbrev KT : Subgroup G := K ⊔ (P : Subgroup G)
abbrev localComponent : Subgroup (KT K P) := K.subgroupOf (KT K P)
def upper : Subrepresentation (ρ.comp (KT K P).subtype) :=
  invariantSubspace ρ (KT K P) I (sup_le hIL hIP)

/-- The KT-action on the literal quotient I/C_I(K). -/
def centralAction : Representation (ZMod 2) (KT K P) (centralQuotient ρ K I) :=
  centralSectionRepresentation ρ K (KT K P) I (sup_le hIL hIP) le_normalizer_of_normal

/-- The canonical quotient map from the selected constituent. -/
def projection : I →ₗ[ZMod 2] centralQuotient ρ K I :=
  ((fixedSpace ρ K).comap I.subtype).mkQ

omit [K.Normal] in
theorem projection_surjective : Function.Surjective (projection ρ K I) :=
  Submodule.mkQ_surjective _

omit [K.Normal] in
theorem projection_ker : LinearMap.ker (projection ρ K I) = (fixedSpace ρ K).comap I.subtype :=
  Submodule.ker_mkQ _

theorem projection_equivariant (g : KT K P) (v : I) :
    projection ρ K I (constituentAction ρ K P I hIL hIP g v) =
      centralAction ρ K P I hIL hIP g (projection ρ K I v) := rfl

/-- Restricting the ambient group changes no fixed vectors or quotient classes. -/
def restrictionEquiv :
    centralQuotient (ρ.comp (KT K P).subtype) (localComponent K P) I ≃ₗ[ZMod 2]
      centralQuotient ρ K I :=
  subgroupCentralQuotientEquiv ρ K (KT K P) le_sup_left I

theorem restrictionEquiv_intertwines (g : KT K P)
    (v : centralQuotient (ρ.comp (KT K P).subtype) (localComponent K P) I) :
    restrictionEquiv ρ K P I
      (normalCentralQuotient (ρ.comp (KT K P).subtype) (localComponent K P)
        (upper ρ K P I hIL hIP) g v) =
    centralAction ρ K P I hIL hIP g (restrictionEquiv ρ K P I v) := by
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

variable (hI : IsIrrPlusWith ρ K P I)

include hI in
/-- Irr⁺ generation excludes trivial component action on the central quotient. -/
theorem component_survives :
    ¬ localComponent K P ≤ (actionHom (centralAction ρ K P I hIL hIP)).ker := by
  intro hk
  apply hI.isIrrPlus.not_le_fixedSpace ρ
  rw [← hI.isIrrPlus.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hkK, v, hv, rfl⟩
  have hfix := (actionHom_eq_one_iff _ (⟨k, (show K ≤ KT K P from le_sup_left) hkK⟩ : KT K P)).mp (hk hkK)
    (Submodule.Quotient.mk (⟨v, hv⟩ : I))
  exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.subtype)).mp hfix

include hI in
/-- Irreducibility is for the actual restricted component action. -/
theorem component_irreducible :
    IsIrreducible ((centralAction ρ K P I hIL hIP).comp (localComponent K P).subtype) := by
  let e : localComponent K P ≃* K := subgroupOfEquivOfLe le_sup_left
  apply (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mp
  exact hI.isIrrPlus.choose_spec.2

variable [IsQuasisimple K]

include hI in
/-- FF descends through the proved equality of action kernels, preserving offender ranks. -/
theorem quotient_ff [Finite V]
    (hff : IsFFModule (imageRepresentation (constituentAction ρ K P I hIL hIP))) :
    IsFFModule (imageRepresentation (centralAction ρ K P I hIL hIP)) := by
  let L := localComponent K P
  let e : L ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  have hi : IsIrrPlus (ρ.comp (KT K P).subtype) L I :=
    (IsIrrPlus.subgroupOf_iff ρ K (KT K P) le_sup_left I).mpr hI.isIrrPlus
  have hf := Quotient.quotient_ff (ρ.comp (KT K P).subtype) L
    (upper ρ K P I hIL hIP) hi hff
  exact image_isFFModule_of_equivariant (centralAction ρ K P I hIL hIP)
    (normalCentralQuotient (ρ.comp (KT K P).subtype) L (upper ρ K P I hIL hIP))
    (MonoidHom.id _) Function.surjective_id (restrictionEquiv ρ K P I)
    (fun g v => (restrictionEquiv_intertwines ρ K P I hIL hIP g v).symm) hf

include hI in
/-- Removing K-fixed vectors loses no part of the constituent action image. -/
theorem action_kernel_eq :
    (actionHom (centralAction ρ K P I hIL hIP)).ker =
      (actionHom (constituentAction ρ K P I hIL hIP)).ker := by
  let L := localComponent K P
  let e : L ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  have hi : IsIrrPlus (ρ.comp (KT K P).subtype) L I :=
    (IsIrrPlus.subgroupOf_iff ρ K (KT K P) le_sup_left I).mpr hI.isIrrPlus
  change (actionHom (centralAction ρ K P I hIL hIP)).ker =
    (actionHom (upper ρ K P I hIL hIP).toRepresentation).ker
  rw [← Quotient.quotient_kernel_eq (ρ.comp (KT K P).subtype) L
    (upper ρ K P I hIL hIP) hi]
  ext g
  change actionHom _ g = 1 ↔ actionHom _ g = 1
  rw [actionHom_eq_one_iff, actionHom_eq_one_iff]
  constructor
  · intro hg v
    apply (restrictionEquiv ρ K P I).injective
    exact (restrictionEquiv_intertwines ρ K P I hIL hIP g v).trans (hg _)
  · intro hg v
    obtain ⟨v, rfl⟩ := (restrictionEquiv ρ K P I).surjective v
    exact (restrictionEquiv_intertwines ρ K P I hIL hIP g v).symm.trans
      (congrArg (restrictionEquiv ρ K P I) (hg v))

variable [Finite G]

omit [IsQuasisimple K] [Finite G] in
theorem outer_two : IsPGroup 2 ((KT K P) ⧸ localComponent K P) := by
  let D := KT K P
  let L := localComponent K P
  let A := (P : Subgroup G).subgroupOf D
  have hgen : A ⊔ L = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show (P : Subgroup G) ≤ D from le_sup_right),
      map_subgroupOf_eq_of_le (show K ≤ D from le_sup_left)]
    rw [sup_comm]
    exact D.range_subtype.symm.trans D.subtype.range_eq_map
  exact quotient_isPGroup_of_sup_eq_top A L P.isPGroup'.comap_subtype hgen

include hI in
/-- The entire generalized Fitting subgroup is the actual quasisimple component image. -/
theorem image_structure [Finite V] :
    IsQuasisimple (actionSubgroup (centralAction ρ K P I hIL hIP) (localComponent K P)) ∧
    IsIrreducible ((imageRepresentation (centralAction ρ K P I hIL hIP)).comp
      (actionSubgroup (centralAction ρ K P I hIL hIP) (localComponent K P)).subtype) ∧
    generalizedFitting (actionImage (centralAction ρ K P I hIL hIP)) =
      actionSubgroup (centralAction ρ K P I hIL hIP) (localComponent K P) := by
  let e : localComponent K P ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (localComponent K P) := IsQuasisimple.of_mulEquiv e.symm
  let : Finite (centralQuotient ρ K I) := Finite.of_surjective _ (projection_surjective ρ K I)
  exact Structure.image_structure (centralAction ρ K P I hIL hIP)
    (localComponent K P) (component_survives ρ K P I hIL hIP hI) (outer_two K P)
    (component_irreducible ρ K P I hIL hIP hI)

variable [Finite V]
local instance quotientFinite : Finite (centralQuotient ρ K I) :=
  Finite.of_surjective _ (projection_surjective ρ K I)

include hI in
/-- SQTK, faithfulness, quasisimplicity of F*, and its irreducibility are all proved. -/
theorem b4 {𝒦 : GroupClass.{u}} (hs : IsSQTK 𝒦 G) (hZ : center K = ⊥) :
    B4Hypotheses 𝒦 (imageRepresentation (centralAction ρ K P I hIL hIP)) := by
  let e : localComponent K P ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (localComponent K P) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (localComponent K P) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro k hk
    have h := (centerCongr e ⟨k, hk⟩).property
    change e k ∈ center K at h
    rw [hZ, mem_bot] at h
    exact mem_bot.mpr (e.injective (h.trans e.map_one.symm))
  obtain ⟨hq, hi, he⟩ := image_structure ρ K P I hIL hIP hI
  refine ⟨Structure.image_sqtk (centralAction ρ K P I hIL hIP)
    (localComponent K P) (component_survives ρ K P I hIL hIP hI) (hs.subgroup (KT K P))
    (outer_two K P) hz, imageRepresentation_injective _, ?_, ?_⟩
  · rw [he]
    exact hq
  · rw [he]
    exact hi

include hI in
/-- Replacement supplies the best offender required by the complete B.4.2 contract. -/
theorem b42 {𝒦 : GroupClass.{u}} (hs : IsSQTK 𝒦 G) (hZ : center K = ⊥)
    (hff : IsFFModule (imageRepresentation (constituentAction ρ K P I hIL hIP))) :
    ∃ A, B42Hypotheses 𝒦 (imageRepresentation (centralAction ρ K P I hIL hIP)) A :=
  (b4 ρ K P I hIL hIP hI hs hZ).exists_bestOffender (quotient_ff ρ K P I hIL hIP hI hff)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
universe u
variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (P : Sylow 2 G) (I : Submodule (ZMod 2) V)
    (hIL : K ≤ subspaceStabilizer ρ I) (hIP : (P : Subgroup G) ≤ subspaceStabilizer ρ I)

abbrev componentImage := actionSubgroup (centralAction ρ K P I hIL hIP) (localComponent K P)

/-- The original K maps to its actual subgroup in the faithful action image. -/
def componentMap : K →* componentImage ρ K P I hIL hIP :=
  ((actionHom (centralAction ρ K P I hIL hIP)).subgroupMap (localComponent K P)).comp
    (subgroupOfEquivOfLe (show K ≤ KT K P from le_sup_left)).symm.toMonoidHom

theorem componentMap_apply (k : K) :
    (componentMap ρ K P I hIL hIP k : actionImage (centralAction ρ K P I hIL hIP)) =
      actionHom (centralAction ρ K P I hIL hIP) (Subgroup.inclusion le_sup_left k) := rfl

theorem componentMap_surjective : Function.Surjective (componentMap ρ K P I hIL hIP) :=
  ((actionHom (centralAction ρ K P I hIL hIP)).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe (show K ≤ KT K P from le_sup_left)).symm.surjective

/-- First isomorphism theorem retaining the full relative central kernel. -/
def componentQuotientEquiv :
    K ⧸ (componentMap ρ K P I hIL hIP).ker ≃* componentImage ρ K P I hIL hIP :=
  QuotientGroup.quotientKerEquivOfSurjective _ (componentMap_surjective ρ K P I hIL hIP)

variable [IsQuasisimple K] (hI : IsIrrPlusWith ρ K P I)
include hI in
/-- The component kernel lies in its intrinsic center. -/
theorem component_kernel_central : (componentMap ρ K P I hIL hIP).ker ≤ center K := by
  let e : localComponent K P ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (localComponent K P) := IsQuasisimple.of_mulEquiv e.symm
  intro k hk
  have hz := Structure.component_kernel_central
    (centralAction ρ K P I hIL hIP) (localComponent K P)
    (component_survives ρ K P I hIL hIP hI) hk
  have hm := (centerCongr e ⟨e.symm k, hz⟩).property
  change e (e.symm k) ∈ center K at hm
  simpa only [e.apply_symm_apply] using hm

include hI in
theorem componentMap_injective (hZ : center K = ⊥) :
    Function.Injective (componentMap ρ K P I hIL hIP) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique (hZ ▸ component_kernel_central ρ K P I hIL hIP hI)

def componentEquiv (hZ : center K = ⊥) : K ≃* componentImage ρ K P I hIL hIP :=
  MulEquiv.ofBijective _ ⟨componentMap_injective ρ K P I hIL hIP hI hZ,
    componentMap_surjective ρ K P I hIL hIP⟩

/-- Under centerlessness, identify the entire F* with the original component. -/
def fittingEquiv [Finite G] [Finite V] (hZ : center K = ⊥) :
    generalizedFitting (actionImage (centralAction ρ K P I hIL hIP)) ≃* K :=
  (MulEquiv.subgroupCongr (image_structure ρ K P I hIL hIP hI).2.2).trans
    (componentEquiv ρ K P I hIL hIP hI hZ).symm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
universe u
variable {G : Type u} [Group G]
    (H K L₁ T V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H))
    (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))

/-- Conditional source inputs. The FF field is the conclusion selected from
F.9.18(4ii), on the actual constituent action image. None of the B.4 outputs
on the central quotient occurs among these premises. -/
structure SourceHypotheses (𝒦 : GroupClass.{u}) : Prop where
  conjugation : SeedAction.IsConjugation H V₃ V₁ ρ
  generation : H = K ⊔ L₁ ⊔ T
  sylow_image : (P : Subgroup (Source.Hstar H)) = Source.starImage H T
  sqtk : IsSQTK 𝒦 H
  quasisimple : IsQuasisimple (Source.starImage H K)
  centerless : center (Source.starImage H K) = ⊥
  selected : IsIrrPlusWith ρ (Source.starImage H K) P I
  invariant : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I
  ff : IsFFModule (imageRepresentation
    (constituentAction
      ρ (Source.starImage H K) P I selected.invariant invariant))

variable {𝒦 : GroupClass.{u}}
    (d : SourceHypotheses H K L₁ T V₃ V₁ ρ P I 𝒦)

/-- Conjugation on U_H/V₁ is still the action underlying the final quotient map. -/
theorem source_projection_conjugation (h : H) (v : Source.UH H V₃)
    (hv : SeedAction.vector H V₃ V₁ v ∈ I)
    (hh : QuotientGroup.mk' (pCore 2 H) h ∈ KT (Source.starImage H K) P) :
    ∃ hv' : SeedAction.vector H V₃ V₁ (SeedAction.conjugate H V₃ h v) ∈ I,
      centralAction ρ (Source.starImage H K) P I d.selected.invariant d.invariant
        ⟨QuotientGroup.mk' (pCore 2 H) h, hh⟩
        (projection ρ (Source.starImage H K) I ⟨SeedAction.vector H V₃ V₁ v, hv⟩) =
      projection ρ (Source.starImage H K) I
        ⟨SeedAction.vector H V₃ V₁ (SeedAction.conjugate H V₃ h v), hv'⟩ := by
  have hv' : SeedAction.vector H V₃ V₁ (SeedAction.conjugate H V₃ h v) ∈ I := by
    rw [← d.conjugation h v]
    exact ((sup_le d.selected.invariant d.invariant) hh _).2 hv
  refine ⟨hv', ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (d.conjugation h v)

variable [Finite G]

omit [(Source.starImage H K).Normal] in
include d in
/-- SQTK descends from the genuine local H through its normal two-core. -/
theorem source_sqtk : IsSQTK 𝒦 (Source.Hstar H) := by
  refine ⟨?_, d.sqtk.isKGroup.quotient (pCore 2 H)⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
    (d.sqtk.stronglyQuasithin p hp ho)

local instance sourceQuotientFinite :
    Finite (centralQuotient ρ (Source.starImage H K) I) :=
  Finite.of_surjective _ (projection_surjective ρ (Source.starImage H K) I)

/-- All four common B.4 premises, on the specified faithful central action image. -/
theorem source_b4 :
    B4Hypotheses 𝒦 (imageRepresentation
      (centralAction ρ (Source.starImage H K) P I d.selected.invariant d.invariant)) := by
  let : IsQuasisimple (Source.starImage H K) := d.quasisimple
  exact b4 ρ (Source.starImage H K) P I d.selected.invariant d.invariant d.selected
    (source_sqtk H K L₁ T V₃ V₁ ρ P I d) d.centerless

/-- Replacement supplies an actual best offender for the complete B.4.2 contract. -/
theorem source_b42 :
    ∃ A, B42Hypotheses 𝒦 (imageRepresentation
      (centralAction ρ (Source.starImage H K) P I d.selected.invariant d.invariant)) A := by
  let : IsQuasisimple (Source.starImage H K) := d.quasisimple
  exact b42 ρ (Source.starImage H K) P I d.selected.invariant d.invariant d.selected
    (source_sqtk H K L₁ T V₃ V₁ ρ P I d) d.centerless d.ff
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage
