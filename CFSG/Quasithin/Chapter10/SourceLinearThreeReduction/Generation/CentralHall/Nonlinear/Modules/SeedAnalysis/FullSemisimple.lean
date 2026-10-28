module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SeedSupport
public import Theory.Representation.CliffordRestriction
public import Theory.Representation.SemisimpleCoinvariants
public import Theory.Representation.BinaryConjugationSection.Coinvariants

/-!
# Semisimplicity and fixed kernels before original seed separation

In the central Hall context, the original full module has no orbit-fixed
part. Minimality of the original setup therefore makes the full maximal
normalizer action irreducible. Clifford restriction through L ◁ L₀ ◁ M
makes its restriction to L semisimple, as well as the literal submodule
W = [V_M,L]. Since [W,L] = W, its fixed part C_W(L) vanishes.

The original moved quotient map is consequently bijective, without any
separation hypothesis. The same coordinates give whole-module orthogonal
and Suzuki rows. In the nonseparated support alternative, W = V_M; both
original components then have zero fixed subgroup on V_M. This removes
the fixed kernels before the tensor analysis, while retaining both original
seed orientations and the literal quotient marking.

Tensor exclusion, the constituent degree bound and reconstruction of the
separated original seed remain with qt-d-10-nona5-central-hall-orders.
No assertion of SeedAnalysisAt is made here.
Source: Clifford restriction (Isaacs, Theorem 6.5); Aschbacher--Smith
D.3.4--7, D.3.21 and 10.1.1, printed pp.195--199,204--207,741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance fullSemisimpleElementary : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
local instance movedSemisimpleElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The unchanged full module under its original maximal normalizer. -/
@[expose] def originalFullAction :
    Representation (ZMod 2) D.maximalLocal (Additive D.fullModule) :=
  elementaryRepresentation
    (D.fullModule.normalizerMonoidHom.comp (inclusion D.maximalLocal_normalizes_fullModule))

/-- The literal L-action on W = [V_M,L], before any central quotient. -/
@[expose] def originalMovedAction :
    Representation (ZMod 2) L (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  elementaryRepresentation ((⁅D.fullModule,L⁆ : Subgroup G).normalizerMonoidHom.comp
    (inclusion (normalizer_commutator_ge_right _ _)))

/-- Identity coordinates on the original full module. -/
def originalFullSection : BinaryConjugationSection D.maximalLocal D.fullModule ⊥
    (originalFullAction D) := {
  section_le := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  kernel_le := bot_le
  normalized := D.maximalLocal_normalizes_fullModule
  coordinates := { toFun v := Multiplicative.ofAdd (Additive.ofMul v)
                   map_one' := rfl
                   map_mul' _ _ := rfl }
  onto := fun v => ⟨v.toAdd.toMul,rfl⟩
  kernel_eq := by ext v; simp
  equivariant := fun _ _ => rfl }

/-- Identity coordinates on the original moved subgroup. -/
def originalMovedSection : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
    (originalMovedAction D) := {
  section_le := source_full_moved_le_component D
  kernel_le := bot_le
  normalized := normalizer_commutator_ge_right _ _
  coordinates := { toFun v := Multiplicative.ofAdd (Additive.ofMul v)
                   map_one' := rfl
                   map_mul' _ _ := rfl }
  onto := fun v => ⟨v.toAdd.toMul,rfl⟩
  kernel_eq := by ext v; simp
  equivariant := fun _ _ => rfl }

/-- Original minimality and the vanishing orbit-fixed part give irreducibility. -/
theorem originalFullAction_irreducible
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (originalFullAction D).IsIrreducible := by
  have hn : D.fullModule ≠ ⊥ := fun hz => D.module_ne_bot
    (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans hz.le))
  let : Nontrivial D.fullModule := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
  apply (originalFullSection D).irreducible_of_subgroup_minimal
  intro J hJV hMJ
  rcases source_minimal_fullModule_eq_or_le_centralizer D c.minimal J hMJ hJV with he | hc
  · exact Or.inl he
  · right
    intro x hx
    have hh : (⟨x,hJV hx⟩ : D.fullModule) ∈ D.fullCentralizer := hc hx
    rw [fullCentralizer_eq_bot_of_central_hstar D c] at hh
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))

/-- Clifford restriction down the actual relative normal chain L ◁ L₀ ◁ M. -/
theorem originalFullAction_component_semisimple
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    IsSemisimpleModule (ZMod 2)[L]
      (Representation.asModule ((originalFullAction D).comp
        (inclusion ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer)))) := by
  let ρ := originalFullAction D
  let K := L.subgroupOf D.maximalLocal
  let N := (localOrbit T L).subgroupOf D.maximalLocal
  have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hn : N ≤ normalizer (K : Set D.maximalLocal) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact Subgroup.mem_normalizer_iff.mp
      (source_nonnormal_orbit_le_normalizer D c.nonnormal hn) k
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  let : IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
    irreducible_restriction_semisimple_of_normal_chain ρ
      (originalFullAction_irreducible D c) K N (comap_mono (le_componentOrbit L T)) hn
  let e : L ≃* K := (subgroupOfEquivOfLe hLM).symm
  exact comp_semisimple_of_surjective (ρ.comp K.subtype) e.toMonoidHom e.surjective

/-- The original moved subgroup is semisimple under L without seed separation. -/
theorem originalMovedAction_semisimple
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    IsSemisimpleModule (ZMod 2)[L] (originalMovedAction D).asModule := by
  let ρ := (originalFullAction D).comp
    (inclusion ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer))
  let := originalFullAction_component_semisimple D c
  let f : (originalMovedAction D).IntertwiningMap ρ := {
    toLinearMap := (inclusion (moved_le_fullModule D)).toAdditive.toZModLinearMap 2
    isIntertwining' _ := by ext v; rfl }
  exact IsSemisimpleModule.of_injective
    (IntertwiningMap.equivLinearMapAsModule _ _ f)
    (by intro x y h; exact Additive.toMul.injective ((inclusion_injective (moved_le_fullModule D)) h))

/-- Semisimplicity and W = [W,L] exclude all L-fixed vectors in W. -/
theorem originalMovedAction_fixed_eq_bot
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (originalMovedAction D).invariants = ⊥ := by
  let := originalMovedAction_semisimple D c
  apply invariants_eq_bot_of_semisimple_of_coinvariants_eq_top
  apply (originalMovedSection D).coinvariants_eq_top_of_group_generation L le_rfl
    (originalMovedAction D) (MonoidHom.id L) (fun _ _ => rfl)
  rw [sup_bot_eq,commutator_comm,source_full_moved_eq_commutator D]

/-- The literal fixed denominator vanishes under the original context alone. -/
theorem movedFixed_eq_bot_of_original_context
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    sourceMovedFixed D = ⊥ := by
  apply bot_unique
  intro w hw
  have hf : Additive.ofMul (⟨w,hw.1⟩ : (⁅D.fullModule,L⁆ : Subgroup G)) ∈
      (originalMovedAction D).invariants := by
    intro l
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * w * (l : G)⁻¹ = w
    rw [hw.2 l l.property,mul_inv_cancel_right]
  rw [originalMovedAction_fixed_eq_bot D c] at hf
  change Additive.ofMul (⟨w,hw.1⟩ : (⁅D.fullModule,L⁆ : Subgroup G)) = 0 at hf
  exact mem_bot.mpr (congrArg (fun v : Additive (⁅D.fullModule,L⁆ : Subgroup G) =>
    (v.toMul : G)) hf)

/-- The original quotient coordinates already mark the whole moved module,
without a crossed-geometry or seed-separation hypothesis. -/
def wholeMovedSection_of_original_context
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((movedQuotientAction D c.nonnormal).comp (QuotientGroup.mk' (pCore 2 L))) :=
  (movedQuotientSection D c.nonnormal).replaceKernel ⊥
    (movedFixed_eq_bot_of_original_context D c)

/-- The literal original quotient map has no kernel in the central Hall context. -/
theorem movedQuotient_coordinates_bijective
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    Function.Bijective (movedQuotientSection D c.nonnormal).coordinates := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_,
    (movedQuotientSection D c.nonnormal).onto⟩
  rw [(movedQuotientSection D c.nonnormal).kernel_eq,
    movedFixed_eq_bot_of_original_context D c,bot_subgroupOf]

/-- Both factors of the nonseparated original seed have zero fixed subgroup
on the entire original full module. -/
theorem full_both_factors_fixed_eq_bot_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
      D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) = ⊥ := by
  have hmove := (full_both_factors_moved_of_not_separated D c ht htn hsep).1
  have hleft : D.fullModule ⊓ centralizer (L : Set G) = ⊥ := by
    have hh := movedFixed_eq_bot_of_original_context D c
    change ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ at hh
    rwa [hmove] at hh
  refine ⟨hleft,?_⟩
  have hh := congrArg (fun J : Subgroup G => J.map (MulAut.conj t).toMonoidHom) hleft
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective,Theory.GroupTheory.map_centralizer_equiv,
    Subgroup.map_bot] at hh
  have hv : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
  rwa [hv] at hh

/-- The original support alternatives, with the literal fixed kernels removed
also in the tensor branch. Both orientations of the original seed are retained. -/
theorem source_crossed_or_fixed_free_tensor_support
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∧
      Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)) ∨
    (⁅D.fullModule,L⁆ = D.fullModule ∧
      ⁅D.fullModule,L.map (MulAut.conj t).toMonoidHom⁆ = D.fullModule ∧
      D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
      D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) = ⊥) := by
  by_cases hs : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)
  · exact Or.inl ⟨full_moved_centralizes_opposite_of_seed_separated D ht htn hs,
      moved_pair_disjoint_of_seed_separated D c ht htn hs⟩
  · obtain ⟨hleft,hright⟩ := full_both_factors_moved_of_not_separated D c ht htn hs
    exact Or.inr ⟨hleft,hright,full_both_factors_fixed_eq_bot_of_not_separated D c ht htn hs⟩

open Representation.OrthogonalFourMinus.FiniteModel
local instance originalFixedBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra _ 2
local instance originalHermitianBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

/-- Apply quotient recognition to the literal Hall rows with every central
kernel discharged before source separation. -/
theorem moduleRow_of_movedQuotientRow_original_context
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (row : MovedQuotientRow D c.nonnormal) : ModuleRow D := by
  cases row with
  | natural r hr e hE =>
    exact .natural r hr e ⟨natural_section_of_movedQuotient D c.nonnormal r e hE.some⟩
  | orthogonal n hn e hE =>
    exact .orthogonal n hn e ⟨(wholeMovedSection_of_original_context D c).relabel
      (QuotientGroup.mk' (pCore 2 L)) hE.some⟩
  | suzuki m hm e hE =>
    exact .suzuki m hm e ⟨(wholeMovedSection_of_original_context D c).relabel
      (QuotientGroup.mk' (pCore 2 L)) hE.some⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
