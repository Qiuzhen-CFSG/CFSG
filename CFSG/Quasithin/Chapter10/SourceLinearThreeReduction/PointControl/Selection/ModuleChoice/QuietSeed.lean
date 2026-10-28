module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalTensor
public import Theory.Representation.PSL3Two.ProductCatalogue
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The original quiet binary-three seed and its ambient displacement

Quiet Thompson action kills the orbit-fixed subgroup, so Irr⁺ minimality
makes the unchanged seed irreducible. The original quotient and its prescribed
Sylow exchanger descend this action to the literal simple square. If neither
component has fixed vectors, both factors act faithfully; the full action
kernel is exactly O₂(L₀). The binary product catalogue then constructs the
actual external tensor coordinates, retaining both independent factor labels.

Embedding this constituent into the original full module shows that every
ambient element moving fewer than nine dimensions preserves it. Source uses
this with the already proved properness to give either actual point selection
or a proper tensor seed and an element moving at least nine dimensions.
Excluding that proper-seed alternative remains necessary for fixed support.

Source: Aschbacher--Smith D.3.5--7, 3.2.6 and10.1.1--3,
printed pp.195--199,581 and741--742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
open BinaryLinearThree.ProductCatalogue
open Representation.QuadraticFourGroup.TensorClassification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem seed_le_full : D.seed ≤ D.fullModule :=
  (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)

/-- Quiet action makes the original Irr⁺ seed genuinely irreducible. -/
theorem quiet_seed_action_irreducible
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    (originalSeedAction D).IsIrreducible := by
  let : Nontrivial D.seed := (Subgroup.nontrivial_iff_ne_bot D.seed).mpr D.seed_ne_bot
  let d : BinaryConjugationSection (localOrbit T L) D.seed ⊥ (originalSeedAction D) := {
    section_le := (le_componentOrbit D.seed T).trans D.module_le_orbit
    kernel_le := bot_le
    normalized := D.orbit_normalizes_seed
    coordinates := {
      toFun v := Multiplicative.ofAdd (Additive.ofMul v)
      map_one' := rfl
      map_mul' _ _ := rfl }
    onto := fun v => ⟨v.toAdd.toMul,rfl⟩
    kernel_eq := by ext v; simp
    equivariant := fun _ _ => rfl }
  apply d.irreducible_of_subgroup_minimal
  intro A hAS hAN
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus A hAS hAN with he | hc
  · exact Or.inl he
  · exact Or.inr ((le_inf (hAS.trans (seed_le_full D)) hc).trans_eq
      (source_fullModule_fixed_eq_bot_of_many D hmany hJ))

/-- The original quotient square acts on the unchanged seed, with both factor formulas. -/
theorem quiet_seed_product_action
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {S : Type*} [Group S] (e : (L ⧸ pCore 2 L) ≃* S)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ q : localOrbit T L →* S × S,
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ σ : Representation (ZMod 2) (S × S) (Additive D.seed),
        σ.IsIrreducible ∧ σ.comp q = originalSeedAction D := by
  obtain ⟨p,hp,hpk,hl,hr⟩ := original_component_product_quotient D hn ht htn
  let c := e.prodCongr e
  let q := c.toMonoidHom.comp p
  have hq : Function.Surjective q := c.surjective.comp hp
  have hk : q.ker = pCore 2 (localOrbit T L) := by
    rw [MonoidHom.ker_comp_of_injective _ c.toMonoidHom c.injective,hpk]
  let ρ := originalSeedAction D
  let : ρ.IsIrreducible := quiet_seed_action_irreducible D hmany hJ
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  have hker : pCore 2 (localOrbit T L) ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let E : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* S × S :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let τ := quotientOfLEKer ρ _ hker
  let σ := τ.comp E.symm.toMonoidHom
  refine ⟨q,hq,hk,?_,?_,σ,?_,?_⟩
  · intro l
    change c (p _) = _
    rw [hl]
    change (e _,e 1) = _
    rw [map_one]
  · intro l
    change c (p _) = _
    rw [hr]
    change (e 1,e _) = _
    rw [map_one]
  · exact (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective τ).mpr
      ((quotientOfLEKer_irreducible_iff ρ _ hker).mpr inferInstance)
  · apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro v
    change τ (E.symm (E (QuotientGroup.mk' _ x))) v = ρ x v
    rw [E.symm_apply_apply]
    rfl

/-- Literal product marking on the unchanged seed, including the full kernel. -/
@[expose] def QuietBinaryThreeSeedMarking
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    {t : G} (ht : t ∈ (T : Subgroup G)) : Prop :=
    ∃ q : localOrbit T L →* BinaryLinearThree.Group × BinaryLinearThree.Group,
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (cL (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,cL (QuotientGroup.mk' _ l))) ∧
      ∃ σ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group)
          (Additive D.seed),
        σ.IsIrreducible ∧ Function.Injective σ ∧ σ.comp q = originalSeedAction D ∧
        (originalSeedAction D).ker = pCore 2 (localOrbit T L) ∧
        ∃ a b : FactorType, Nonempty (σ.Equiv (externalTensor a.action b.action)) ∧
          Module.finrank (ZMod 2) (Additive D.seed) = a.degree * b.degree

/-- Absence of component-fixed vectors forces a faithful tensor marking on
 the original seed, with the full orbit-action kernel retained. -/
theorem quiet_binaryThree_seed_marking_of_no_component_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    QuietBinaryThreeSeedMarking D cL ht := by
  have hfix' : D.fullModule ⊓ centralizer
      (L.map (MulAut.conj t).toMonoidHom : Set G) = ⊥ := by
    rw [←quiet_component_fixed_conjugate D ht,hfix,Subgroup.map_bot]
  have hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) := by
    rintro (hc | hc)
    · exact D.seed_ne_bot (bot_unique ((le_inf (seed_le_full D) hc).trans_eq hfix'))
    · exact D.seed_ne_bot (bot_unique ((le_inf (seed_le_full D) hc).trans_eq hfix))
  obtain ⟨q,hq,hk,hl,hr,σ,hirr,hσ⟩ := quiet_seed_product_action D hmany hn hJ cL ht htn
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hf := original_seed_product_faithful_of_not_separated D cL ht hsep q hl hr σ hσ
  have hkernel : (originalSeedAction D).ker = pCore 2 (localOrbit T L) := by
    rw [←hσ,MonoidHom.ker_comp_of_injective _ _ hf,hk]
  let := hirr
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨g,hg⟩ := exists_ne (1 : BinaryLinearThree.Group)
  have hleft : ∃ g, σ (g,1) ≠ 1 :=
    ⟨g,fun hh => hg (congrArg Prod.fst (hf (hh.trans σ.map_one.symm)))⟩
  have hright : ∃ g, σ (1,g) ≠ 1 :=
    ⟨g,fun hh => hg (congrArg Prod.snd (hf (hh.trans σ.map_one.symm)))⟩
  obtain ⟨a,b,⟨e⟩⟩ := classify_moving_product σ hleft hright
  exact ⟨q,hq,hk,hl,hr,σ,hirr,hf,hσ,hkernel,a,b,⟨e⟩,finrank_of_marking σ a b e⟩

private def seedInFull : Additive D.seed →ₗ[ZMod 2] Additive D.fullModule :=
  (inclusion (seed_le_full D)).toAdditive.toZModLinearMap 2

private theorem seedInFull_injective : Function.Injective (seedInFull D) := by
  intro v w he
  exact Additive.toMul.injective ((inclusion_injective (seed_le_full D)) he)

private def seedInFullIntertwiner :
    Representation.IntertwiningMap ((originalSeedAction D).comp
      (subgroupOfEquivOfLe (localOrbit T L).le_normalizer).toMonoidHom)
      ((originalFullAction D).comp ((localOrbit T L).subgroupOf D.maximalLocal).subtype) where
  toLinearMap := seedInFull D
  isIntertwining' _ := by ext v; rfl

private theorem seedInFull_range_irreducible
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) : (seedInFullIntertwiner D).range.toRepresentation.IsIrreducible := by
  let e := subgroupOfEquivOfLe (localOrbit T L).le_normalizer
  let τ : Representation (ZMod 2) ((localOrbit T L).subgroupOf D.maximalLocal)
      (Additive D.seed) := (originalSeedAction D).comp e.toMonoidHom
  let : τ.IsIrreducible := (irreducible_comp_surjective_iff e.toMonoidHom e.surjective
    (originalSeedAction D)).mpr (quiet_seed_action_irreducible D hmany hJ)
  let f := seedInFullIntertwiner D
  let a : τ.Equiv f.range.toRepresentation := Representation.Equiv.mk
    (LinearEquiv.ofInjective f.toLinearMap (seedInFull_injective D)) (fun _ => by ext v; rfl)
  exact (RepEquiv.ofRepresentationEquiv a.symm).irreducible_of_euqiv inferInstance

/-- Small displacement on the full module forces preservation of the original seed. -/
theorem quiet_seed_stable_of_full_displacement_lt
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (m : D.maximalLocal)
    (hsmall : operatorFixedCodim (originalFullAction D m) <
      Module.finrank (ZMod 2) (Additive D.seed)) :
    (m : G) ∈ normalizer (D.seed : Set G) := by
  let N := (localOrbit T L).subgroupOf D.maximalLocal
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  have hr : Module.finrank (ZMod 2) (seedInFullIntertwiner D).range.toSubmodule =
      Module.finrank (ZMod 2) (Additive D.seed) :=
    (LinearEquiv.ofInjective (seedInFull D) (seedInFull_injective D)).finrank_eq.symm
  have hs := map_constituent_eq_self_of_displacement_lt (originalFullAction D) N m
    (seedInFullIntertwiner D).range (seedInFull_range_irreducible D hmany hJ)
    (by simpa only [operatorFixedCodim, Module.End.one_eq_id, hr] using hsmall)
  apply mem_normalizer_iff.mpr
  intro v
  constructor
  · intro hv
    have hh : seedInFull D (Additive.ofMul ⟨v,hv⟩) ∈
        (seedInFullIntertwiner D).range.toSubmodule := ⟨_,rfl⟩
    have hm : originalFullAction D m (seedInFull D (Additive.ofMul ⟨v,hv⟩)) ∈
        (seedInFullIntertwiner D).range.toSubmodule := hs ▸ Submodule.mem_map_of_mem hh
    obtain ⟨w,hw⟩ := hm
    have he := congrArg (fun a : Additive D.fullModule => (a.toMul : G)) hw
    change (w.toMul : G) = (m:G)*v*(m:G)⁻¹ at he
    exact he ▸ w.toMul.property
  · intro hv
    have hV : v ∈ D.fullModule := (mem_normalizer_iff.mp
      (D.maximalLocal_normalizes_fullModule m.property) v).mpr ((seed_le_full D) hv)
    have hh : seedInFull D (Additive.ofMul ⟨(m:G)*v*(m:G)⁻¹,hv⟩) ∈
        (seedInFullIntertwiner D).range.toSubmodule := ⟨_,rfl⟩
    rw [←hs] at hh
    obtain ⟨w,hw,he⟩ := hh
    obtain ⟨z,hz⟩ := hw
    have he' : w = Additive.ofMul ⟨v,hV⟩ := (apply_bijective (originalFullAction D) m).injective he
    have hz' := congrArg (fun a : Additive D.fullModule => (a.toMul : G)) (hz.trans he')
    change (z.toMul : G) = v at hz'
    exact hz' ▸ z.toMul.property


/-- Every full-action element moving fewer than nine dimensions preserves the
original seed in the branch with no component-fixed vectors. -/
theorem quiet_binaryThree_seed_stable_of_displacement_lt_nine
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥)
    (m : D.maximalLocal)
    (hsmall : operatorFixedCodim (originalFullAction D m) < 9) :
    (m : G) ∈ normalizer (D.seed : Set G) := by
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨q,hq,hk,hl,hr,σ,hi,hf,hσ,hkernel,a,b,he,hd⟩ :=
    quiet_binaryThree_seed_marking_of_no_component_fixed D hmany hn hJ cL hfix ht htn
  have hdim : 9 ≤ Module.finrank (ZMod 2) (Additive D.seed) := by
    rw [hd]
    cases a <;> cases b <;> decide
  exact quiet_seed_stable_of_full_displacement_lt D hmany hJ m (hsmall.trans_le hdim)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
