module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Quasithin.Rank

/-!
# The component in the faithful central-section action

A nontrivial image of a normal quasisimple component is quasisimple. When
that component acts irreducibly, so does the faithful full action image;
its two-core is therefore trivial. If the quotient above the component is
a two-group, the component image is the entire generalized Fitting subgroup.

The component map and its central kernel are retained explicitly. If the
original component is centerless, it embeds in the image; the whole action
kernel then embeds in the outer two-group quotient. SQTK descends through
this two-group kernel, using odd-prime rank transport and the actual K-group
hypothesis. No order or simplicity certification of a model is needed.

Source: Aschbacher–Smith, F.9.18(3–4), printed pp.325–326, and the B.4.2
application in 13.8.20, printed pp.954–955. The group argument follows the
checked irreducible-image calculation in NaturalSections/Recognition.lean
for the SL₃(4) branch, without its model-specific classification inputs.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory CFSG.Quasithin

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
  [IsQuasisimple K] (hsurvive : ¬ K ≤ (actionHom ρ).ker)

instance componentImage_normal : (actionSubgroup ρ K).Normal :=
  Subgroup.Normal.map inferInstance _ ρ.asGroupHom.rangeRestrict_surjective

/-- The component map retains its actual relative kernel. -/
def componentMap : K →* actionSubgroup ρ K :=
  (actionHom ρ).subgroupMap K

omit [Finite G] [Finite V] [IsQuasisimple K] [K.Normal] in
theorem componentMap_surjective : Function.Surjective (componentMap ρ K) :=
  (actionHom ρ).subgroupMap_surjective K

def componentQuotientEquiv :
    K ⧸ (componentMap ρ K).ker ≃* actionSubgroup ρ K :=
  QuotientGroup.quotientKerEquivOfSurjective _ (componentMap_surjective ρ K)

omit [Finite G] [Finite V] in
include hsurvive in
theorem component_kernel_central : (componentMap ρ K).ker ≤ center K := by
  intro k hk
  have hk' : k.val ∈ (actionHom ρ).ker := congrArg Subtype.val hk
  have hc : (k : G) ∈ centralizer (K : Set G) := by
    have hcomp : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
    have hcomm := (hcomp.normal_dichotomy (actionHom ρ).ker).resolve_left hsurvive
    exact (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hcomm)) hk'
  exact mem_center_iff.mpr (fun l => Subtype.ext (mem_centralizer_iff.mp hc l l.property))

omit [Finite G] [Finite V] in
include hsurvive in
theorem component_injective (hZ : center K = ⊥) : Function.Injective (componentMap ρ K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique (hZ ▸ component_kernel_central ρ K hsurvive)

def componentEquiv (hZ : center K = ⊥) : K ≃* actionSubgroup ρ K :=
  MulEquiv.ofBijective _ ⟨component_injective ρ K hsurvive hZ, componentMap_surjective ρ K⟩

omit [Finite G] [Finite V] in
private theorem irreducible_of_component (σ : Representation (ZMod 2) G V)
    (L : Subgroup G) [IsIrreducible (σ.comp L.subtype)] : IsIrreducible σ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (σ.comp L.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (σ.comp L.subtype) :=
    ⟨S.toSubmodule, fun l _ hv => S.apply_mem_toSubmodule l hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (σ.comp L.subtype) => U.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (σ.comp L.subtype) => U.toSubmodule) h)

include hsurvive in
theorem image_structure (hquot : IsPGroup 2 (G ⧸ K))
    (hi : IsIrreducible (ρ.comp K.subtype)) :
    IsQuasisimple (actionSubgroup ρ K) ∧
    IsIrreducible ((imageRepresentation ρ).comp
      (actionSubgroup ρ K).subtype) ∧
    generalizedFitting (actionImage ρ) =
      actionSubgroup ρ K := by
  let σ := ρ
  let f := actionHom σ
  let L := actionSubgroup σ K
  let : L.Normal := componentImage_normal ρ K
  let : Nontrivial L := (nontrivial_iff_ne_bot _).2
    (fun h => hsurvive ((map_eq_bot_iff K).mp h))
  let : IsQuasisimple L := IsQuasisimple.of_surjective (f.subgroupMap K) (f.subgroupMap_surjective K)
  have hLI : IsIrreducible ((imageRepresentation σ).comp L.subtype) :=
    (irreducible_comp_surjective_iff (f.subgroupMap K) (f.subgroupMap_surjective K)
      ((imageRepresentation σ).comp L.subtype)).mp hi
  let := hLI
  let : IsIrreducible (imageRepresentation σ) := irreducible_of_component _ L
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : pCore 2 (actionImage σ) = ⊥ := le_bot_iff.mp
    ((normal_p_subgroup_le_ker (imageRepresentation σ) (pCore 2 (actionImage σ)) pCore_isPGroup).trans
      ((MonoidHom.ker_eq_bot_iff _).mpr (imageRepresentation_injective σ)).le)
  have hquo : IsPGroup 2 (actionImage σ ⧸ L) := hquot.of_surjective
    (QuotientGroup.map K L f (Subgroup.le_comap_map _ _))
    (QuotientGroup.map_surjective_of_surjective K L f
      (QuotientGroup.mk_surjective.comp σ.asGroupHom.rangeRestrict_surjective) _)
  exact ⟨inferInstance, hLI, generalizedFitting_eq_of_quasisimple_two_quotient L hquo hcore⟩

omit [Finite G] [Finite V] in
include hsurvive in
theorem kernel_two (hquot : IsPGroup 2 (G ⧸ K)) (hZ : center K = ⊥) :
    IsPGroup 2 (actionHom ρ).ker := by
  let f := actionHom ρ
  have hf := component_injective ρ K hsurvive hZ
  apply hquot.of_injective ((QuotientGroup.mk' K).comp f.ker.subtype)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  apply Subtype.ext
  have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
  have he : componentMap ρ K ⟨x, hxK⟩ = componentMap ρ K 1 := by
    apply Subtype.ext
    change f x = f 1
    rw [map_one]
    exact x.property
  exact congrArg (fun k : K => (k : G)) (hf he)

omit [Finite V] in
include hsurvive in
theorem image_sqtk {𝒦 : GroupClass.{u}} (hs : CFSG.Quasithin.IsSQTK 𝒦 G)
    (hquot : IsPGroup 2 (G ⧸ K)) (hZ : center K = ⊥) :
    CFSG.Quasithin.IsSQTK 𝒦 (actionImage ρ) := by
  let f := actionHom ρ
  have hSQ : CFSG.Quasithin.IsSQTK 𝒦 (G ⧸ f.ker) := by
    refine ⟨?_, hs.isKGroup.quotient f.ker⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho f.ker
      (kernel_two ρ K hsurvive hquot hZ)).trans (hs.stronglyQuasithin p hp ho)
  exact (CFSG.Quasithin.IsSQTK.equiv (QuotientGroup.quotientKerEquivOfSurjective f
    ρ.asGroupHom.rangeRestrict_surjective)).mp hSQ
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
