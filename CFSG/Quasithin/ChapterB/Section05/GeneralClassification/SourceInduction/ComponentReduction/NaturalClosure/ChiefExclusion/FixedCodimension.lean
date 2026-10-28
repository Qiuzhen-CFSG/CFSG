module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedCodimension.Basic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedCodimension.GenerationContract
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedCodimension.InvariantFlags
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedCodimension.ThreeInvolutions
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.MinimumDegree
public import Theory.Representation.SL2SevenCentralProductOffenders
public import Theory.ElementaryAbelian.Quotient

/-!
# Invariant chief flags and sharp fixed-codimension estimates

Three conjugate involutions span the commutator module by their displacement
images. The proved 3m minimum degree then gives codimension at least m for a
nontrivial elementary subgroup on any nontrivial irreducible L-module. The
actual projection lemma applies this bound to every literal LA-section of
an invariant L-chief flag, and the published telescope yields inequality (!).

The seed's odd field degree discharges the proved matrix-generation theorem.
The two component projections also give exhaustive A-stable L-chief flags,
including a flag of V adapted to any prescribed LA-subrepresentation. Both
flag constructions are applied below to the literal fixed space C_V(C_A(L)).
The natural-seed estimate `seed_fixedCodim_lower` is re-exported from `Basic`
with the actual A-subgroup of LA acting on the seed.

All conclusions use the original setup, component, commutator, natural seed
and given second component. No further classification, flag-existence,
generation or numerical premise remains. Constructing the second component
and completing the final sharp-rank contradiction belong to the parent
chief-exclusion argument. The earlier conditional APIs are preserved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, inequality (!).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

private theorem irreducible_full_commutator
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) H W) [IsIrreducible τ] (hne : τ ≠ 1) :
    subspaceCommutator τ ⊤ ⊤ = ⊤ := by
  let C : Subrepresentation τ := {
    toSubmodule := subspaceCommutator τ ⊤ ⊤
    apply_mem_toSubmodule g v hv :=
      (subspaceCommutator_invariant τ ⊤ ⊤ (mem_top g) v).2 hv }
  rcases eq_bot_or_eq_top C with hz | ht
  · exfalso
    apply hne
    have hc := congrArg Subrepresentation.toSubmodule hz
    have hf := (subspaceCommutator_eq_bot_iff τ ⊤ ⊤).mp hc
    ext g v
    exact hf Submodule.mem_top ⟨g, mem_top g⟩
  · exact congrArg Subrepresentation.toSubmodule ht

/-- Three conjugates and the proved 3m minimum degree give the sharp bound
on every nontrivial L-irreducible action. The only extra input is explicit
generation in the actual matrix group; no marking of the module is assumed. -/
theorem irreducible_fixedCodim_lower_of_generation [Finite G]
    {A L : Subgroup G} (s : NaturalSeed ρ A L) (hL : IsComponent G L)
    (hgen : ThreeInvolutionGeneration s.field)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (τ : Representation (ZMod 2) L W) [IsIrreducible τ] (hne : τ ≠ 1)
    (B : Subgroup L) (hB : IsElementaryAbelian 2 B) (hBn : B ≠ ⊥) :
    s.field.degree ≤ fixedCodim τ B := by
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBn
  have htne : t ≠ 1 := fun he => ht1 (Subtype.ext he)
  let : IsElementaryAbelian 2 B := hB
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  let e := s.natural.groupEquiv
  obtain ⟨g, h, hgh⟩ := hgen (e t) (by rw [← map_pow, ht2, map_one])
    (fun ht0 => htne (e.injective (ht0.trans e.map_one.symm)))
  have hgenL : (⊤ : Subgroup L) ≤
      zpowers t ⊔ zpowers (e.symm g * t * (e.symm g)⁻¹) ⊔
        zpowers (e.symm h * t * (e.symm h)⁻¹) := by
    have heq := congrArg (Subgroup.map e.symm.toMonoidHom) hgh
    simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      map_mul, map_inv, e.symm_apply_apply, Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]
      using heq.symm.le
  have hu := SL2SevenCentralProduct.finrank_le_three_mul_fixedCodim_of_three_conjugates
    τ ⊤ (irreducible_full_commutator τ hne) t (e.symm g) (e.symm h) hgenL
  have hl := natural_component_min_degree ρ s hL τ hne
  have hb := NaturalTensor.fixedCodim_mono τ (zpowers_le.mpr ht)
  omega

/-- The conditional source consumer on each literal LA-section of an
invariant L-chief flag. `factorCodim_lower` discharges generation below. -/
theorem InvariantChiefFlag.factorCodim_lower_of_generation [Finite G]
    [Module.Finite (ZMod 2) V] {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (hgen : ThreeInvolutionGeneration s.field)
    {S : Submodule (ZMod 2) V} (f : InvariantChiefFlag ρ A L S)
    {i : ℕ} (hi : i ∈ f.noncentral) : s.field.degree ≤ f.factorCodim i := by
  let p := d.projections ρ s hL
  have hc : L ≤ centralizer (d.second : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hL.commutator_eq_bot_of_ne d.isComponent d.distinct)
  let τ := f.factorAction i
  let j : L →* ↥(L ⊔ A) := Subgroup.inclusion le_sup_left
  have he : τ.comp j =
      sectionRepresentation (ρ.comp L.subtype) (f.term i) (f.term (i + 1)) :=
    f.factorAction_comp_component ρ i
  let : IsIrreducible (τ.comp j) := he.symm ▸ f.chief i (f.noncentral_mem.mp hi).1
  change s.field.degree ≤ fixedCodim τ (A.subgroupOf (L ⊔ A))
  rw [p.fixedCodim_eq_left hc setup.minimal.1.1.2 τ]
  apply irreducible_fixedCodim_lower_of_generation ρ s hL hgen (τ.comp j)
  · intro hz
    apply (f.noncentral_mem.mp hi).2
    intro l v
    rw [← he, hz]
    rfl
  · let : IsElementaryAbelian 2 A := setup.minimal.1.1.2
    exact IsElementaryAbelian.of_surjective p.left.rangeRestrict p.left.rangeRestrict_surjective
  · apply p.leftRange_ne_bot hc ?_ hLA
    let : IsQuasisimple L := hL.2
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance

/-- Inequality (!) for the literal flag, conditional only on the stated
matrix-group generation input. -/
theorem InvariantChiefFlag.count_mul_le_of_generation [Finite G]
    [Module.Finite (ZMod 2) V] {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (hgen : ThreeInvolutionGeneration s.field)
    {S : Submodule (ZMod 2) V} (f : InvariantChiefFlag ρ A L S) :
    f.noncentral.card * s.field.degree ≤ fixedCodim ρ A :=
  f.count_mul_le_fixedCodim s.field.degree
    (fun _ hi => f.factorCodim_lower_of_generation ρ setup hL hLA s d hgen hi)

/-- The sharp m bound for every nontrivial irreducible L-module and every
nontrivial elementary two-subgroup of L. The seed's odd degree supplies
generation by three conjugate involutions in the actual component. -/
theorem irreducible_fixedCodim_lower [Finite G]
    {A L : Subgroup G} (s : NaturalSeed ρ A L) (hL : IsComponent G L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (τ : Representation (ZMod 2) L W) [IsIrreducible τ] (hne : τ ≠ 1)
    (B : Subgroup L) (hB : IsElementaryAbelian 2 B) (hBn : B ≠ ⊥) :
    s.field.degree ≤ fixedCodim τ B :=
  irreducible_fixedCodim_lower_of_generation ρ s hL
    (seed_threeInvolutionGeneration ρ s) τ hne B hB hBn

/-- Each noncentral chief factor has A-fixed codimension at least m for its
literal LA-quotient action. Finite dimensionality comes from the setup. -/
theorem InvariantChiefFlag.factorCodim_lower [Finite G]
    {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    {S : Submodule (ZMod 2) V} (f : InvariantChiefFlag ρ A L S)
    {i : ℕ} (hi : i ∈ f.noncentral) : s.field.degree ≤ f.factorCodim i := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  exact f.factorCodim_lower_of_generation ρ setup hL hLA s d
    (seed_threeInvolutionGeneration ρ s) hi

/-- The fixed-codimension half of source inequality (!) for every invariant
chief flag, with all generation and local estimates discharged. -/
theorem InvariantChiefFlag.count_mul_le [Finite G]
    {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    {S : Submodule (ZMod 2) V} (f : InvariantChiefFlag ρ A L S) :
    f.noncentral.card * s.field.degree ≤ fixedCodim ρ A := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  exact f.count_mul_le_fixedCodim s.field.degree
    (fun _ hi => f.factorCodim_lower ρ setup hL hLA s d hi)

/-- Complete inequality (!) follows since the original minimal best offender
has fixed codimension at most its rank. -/
theorem InvariantChiefFlag.count_mul_le_rank [Finite G]
    {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    {S : Submodule (ZMod 2) V} (f : InvariantChiefFlag ρ A L S) :
    f.noncentral.card * s.field.degree ≤ rank A := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  exact (f.count_mul_le ρ setup hL hLA s d).trans (setup.minimal.1.isOffender ρ).2

/-- Choose an exhaustive flag of V through the prescribed LA-subrepresentation,
with the two sharp estimates on every literal noncentral section. -/
theorem exists_invariantChiefFlag_through_with_bounds [Finite G]
    {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (S : Subrepresentation (ρ.comp (L ⊔ A).subtype)) :
    ∃ f : InvariantChiefFlag ρ A L ⊤, ∃ r ≤ f.length,
      (f.term r).toSubmodule = S.toSubmodule ∧
      ∀ i ∈ f.noncentral, 3 * s.field.degree ≤ f.factorDimension i ∧
        s.field.degree ≤ f.factorCodim i := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  obtain ⟨f, r, hr, he⟩ := exists_invariantChiefFlag_through ρ setup hL s d S
  exact ⟨f, r, hr, he, fun _ hi =>
    ⟨f.factorDimension_lower ρ s hL hi, f.factorCodim_lower ρ setup hL hLA s d hi⟩⟩

/-- The literal fixed space C_V(A ∩ C_G(L)) has an exhaustive invariant
chief flag satisfying both sharp estimates, as needed in (!!). -/
theorem exists_offenderCentralizerFixed_invariantChiefFlag_with_bounds [Finite G]
    {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L) :
    ∃ f : InvariantChiefFlag ρ A L (fixedSpace ρ (A ⊓ centralizer (L : Set G))),
      ∀ i ∈ f.noncentral, 3 * s.field.degree ≤ f.factorDimension i ∧
        s.field.degree ≤ f.factorCodim i := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  obtain ⟨f⟩ := exists_offenderCentralizerFixed_invariantChiefFlag ρ setup hL s d
  exact ⟨f, fun _ hi =>
    ⟨f.factorDimension_lower ρ s hL hi, f.factorCodim_lower ρ setup hL hLA s d hi⟩⟩

/-- The exhaustive flag of V adapted to C_V(A ∩ C_G(L)), with both sharp
estimates on its actual sections. This is the flag used to compare counts
inside and outside that fixed space in the final source argument. -/
theorem exists_invariantChiefFlag_through_offenderCentralizerFixed_with_bounds [Finite G]
    {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L) :
    ∃ f : InvariantChiefFlag ρ A L ⊤, ∃ r ≤ f.length,
      (f.term r).toSubmodule = fixedSpace ρ (A ⊓ centralizer (L : Set G)) ∧
      ∀ i ∈ f.noncentral, 3 * s.field.degree ≤ f.factorDimension i ∧
        s.field.degree ≤ f.factorCodim i :=
  exists_invariantChiefFlag_through_with_bounds ρ setup hL hLA s d
    (offenderCentralizerFixedOver ρ setup.minimal.1.1.2)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
