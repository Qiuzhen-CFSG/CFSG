module

public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionOffender
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Quasisimple central sections and offenders

For a quasisimple subgroup L normalized by H, the kernel of H on an invariant
Irr⁺ section I/C_I(L) centralizes L. Indeed, trivial action by L would make
[I,L] central, contradicting perfectness and noncentrality of I. The normal
kernel therefore centralizes the component L of H. All normality is relative
to H, and all actions are induced on the literal central quotient.

A best offender A ≤ H disjoint from C_G(L) consequently acts faithfully on
this quotient. The fixed-codimension comparison for sections supplies a best
offender in its action image and hence an FF-module. The source assembly
proves that disjointness after its two-core reduction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.5(8) and B.1.11, printed pp. 69–70 and 72–73.
-/

public section
namespace Representation.BinaryOffender
open Subgroup Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A quasisimple actor normal in H has section kernel centralizing L. -/
theorem centralSection_kernel_le_centralizer (L H : Subgroup G) [IsQuasisimple L]
    (hLH : L ≤ H) (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)) :
    (centralSectionRepresentation ρ L H I hHI hHN).ker.map H.subtype ≤
      H ⊓ centralizer (L : Set G) := by
  let L₀ := L.subgroupOf H
  let : L₀.Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  let : IsQuasisimple L₀ := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLH).symm
  let σ := centralSectionRepresentation ρ L H I hHI hHN
  have hnon : ¬ L₀ ≤ σ.ker := by
    intro hk
    apply hI.not_le_fixedSpace ρ
    apply le_fixedSpace_of_commutator_le_fixedSpace ρ L I hI.choose
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, v, hv, rfl⟩
    exact (centralSectionRepresentation_ker_iff ρ L H I hHI hHN ⟨l, hLH hl⟩).mp
      (hk hl) v hv
  have hcomp : IsComponent H L₀ := ⟨(inferInstance : L₀.Normal).isSubnormal, inferInstance⟩
  have hc : σ.ker ≤ centralizer (L₀ : Set H) := by
    rcases hcomp.normal_dichotomy σ.ker with hn | hc
    · exact (hnon hn).elim
    · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hc)
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨h.property, mem_centralizer_iff.mpr ?_⟩
  intro l hl
  exact congrArg Subtype.val ((mem_centralizer_iff.mp (hc hh)) ⟨l, hLH hl⟩ hl)

/-- A best offender disjoint from the centralizer of L supplies an offender
on the faithful image of any invariant Irr⁺ section. -/
theorem centralSection_isFFModule_of_offender (L A H : Subgroup G) [IsQuasisimple L]
    (hA : IsBestOffender ρ A) (hLH : L ≤ H) (hAH : A ≤ H)
    (hdis : Disjoint A (centralizer (L : Set G)))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)) :
    IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) := by
  let τ := ρ.comp H.subtype
  let W := invariantSubspace ρ H I hHI
  let U : Subrepresentation τ := ⟨fixedSpace ρ L, fun h _ hv =>
    (fixedSpace_stable_of_normalizes ρ hHN h.property _).2 hv⟩
  have hA₀ := hA.subgroupOf ρ hAH
  have hk := centralSection_kernel_le_centralizer ρ L H hLH I hI hHI hHN
  have hf : ∀ a ∈ A.subgroupOf H,
      (∀ s, sectionRepresentation τ U W a s = s) → a = 1 := by
    intro a ha hs
    have haK : a ∈ (centralSectionRepresentation ρ L H I hHI hHN).ker := by
      apply LinearMap.ext
      exact hs
    have haC := (hk (mem_map_of_mem H.subtype haK)).2
    apply Subtype.ext
    exact disjoint_iff_inf_le.mp hdis ⟨ha, haC⟩
  obtain ⟨B, _, hB⟩ := hA₀.section_contains_bestOffender τ U W hf
  exact ⟨B, hB.isOffender _⟩
end Representation.BinaryOffender
