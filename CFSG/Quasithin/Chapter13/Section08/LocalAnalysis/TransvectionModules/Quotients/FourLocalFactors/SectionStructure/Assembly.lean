module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.SectionStructure.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.CoreBounds
public import Theory.GroupTheory.CComponent.Basic

/-!
# Source assembly of the quotient structure in 13.8.6(4)

The two natural actions remain distinct: NaturalSetup describes the original
L-module V, while ConjugationSection and its marked equivariant equivalence
describe the literal U_H/V₁ and the actual K* in H/O₂(H). The hypothesis H=KT
is a set product. Subnormal perfectness then proves K normal in H.

Irreducibility of the original module proves V=⟨V₃^L⟩. The earlier global
abelianness of ⟨V^{G₁}⟩ and the universally supplied 13.7.3(3) core bound
apply to the chosen H in the actual Hz. SourceAction proves the kernel
commutator bound from the marked natural model, and SectionStructure turns
these results into relative normality, elementary abelianness of U_L/V,
all four normalization statements, and its actual bar-image representation.
The source identities for I₂ and O²(I₂) give the normalization of U₂.
No commutator conclusion or quotient structure is included as an input.

Data is the constructed output, not a source hypothesis. Its symmetric-action
method uses the specified isomorphism of the actual bar image with S₆ and
retains the canonical conjugation formula. This completes the section/action
part of 13.8.6(4); the two local-plane identifications and Steinberg quotient
belong to the parent development.

Source: Aschbacher–Smith (1 March 2004), printed p.948 (PDF p.965), with
13.5.2(3), 13.5.4(1),(6), 13.7.3(3), 13.7.6(3), 13.8.2 and F.9.2(3).
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.SectionStructure
open ComponentSieve.SixAndG2.NaturalSix
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- The constructed literal section and its full and local normalizers.
The action is on the actual image in Notation 12.2.5(2). -/
structure Data (L H T L₁ L₂ V V₂ V₃ : Subgroup G) where
  contains : V ≤ Source.UL L H V₃
  normal : (V.subgroupOf (Source.UL L H V₃)).Normal
  elementary : let _ := normal; IsElementaryAbelian 2 (Source.ULsection L H V₃ V)
  normalizes_UL : L ⊔ T ≤ normalizer (Source.UL L H V₃ : Set G)
  normalizes_V : L ⊔ T ≤ normalizer (V : Set G)
  normalizes_UH : L₁ ⊔ T ≤ normalizer (Source.UH H V₃ : Set G)
  normalizes_U2 : L₂ ⊔ T ≤ normalizer (Source.U2 H V V₂ : Set G)
  kernel_commutator : ⁅Source.UL L H V₃,
    (barKernel (L ⊔ T) V).map (L ⊔ T).subtype⁆ ≤ V
  action :
    let _ := normal
    let _ := elementary
    Representation (ZMod 2) (barMap (L ⊔ T) V normalizes_V).range
      (Additive (Source.ULsection L H V₃ V))
  conjugation :
    let _ := normal
    let _ := elementary
    SectionConjugationAlong (L ⊔ T) (Source.UL L H V₃) V
      (barMap (L ⊔ T) V normalizes_V).rangeRestrict normalizes_UL action

/-- The source structure from the actual two natural modules and marked flag.
The earlier input 13.8.2 is restricted to H, and universal 13.7.3(3) is
used at the supplied member H of the literal Hz. Component normality is
derived from the literal product H=KT and subnormal perfectness.
The remaining earlier identities are C_V(L)=1, C_T(V)=O₂(LT), the exact
F.9.2(3) kernel, and the 13.5.4 description of I₂ and its residual. -/
theorem exists_source_structure
    (L H K T L₁ L₂ G₁ M I₂ V V₁ V₂ V₃ : Subgroup G)
    [Finite G] [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V G₁)]
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hHK : (H : Set G) = (K : Set G) * (T : Set G))
    (hK : (K.subgroupOf H).IsCComponent)
    (hcores : ∀ J ∈ Source.Hz L₁ T G₁ M,
      Source.UL L J V₃ ≤ (L ⊔ T).pCoreIn 2)
    (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hCT : T ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2)
    (hline : V₁ ≠ ⊥) (h13 : V₁ ≤ V₃) (h3V : V₃ ≤ V)
    (hT₂ : T ≤ normalizer (V₂ : Set G)) (hL₂ : L₂ ≤ L)
    (hI : I₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
      (normalizer (V₂ : Set G)))
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hker : ∀ h : H, (∀ u : Source.UH H V₃, ⁅(h : G), (u : G)⁆ ∈ V₁) → h ∈ pCore 2 H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k : Source.starImage H K, ∀ u, E (ρ k u) = alternatingAction (eK k) (E u))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane) :
    Nonempty (Data L H T L₁ L₂ V V₂ V₃) := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.2
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hHK]
    exact ⟨k, hk, 1, T.one_mem, mul_one k⟩
  let _ := component_normal_of_product H K T hKH hTH hK
    (original_sylow_isPGroup L T V V₁ n) (by
      intro h
      have hm : (h : G) ∈ (K : Set G) * (T : Set G) := hHK ▸ h.property
      exact hm)
  let _ : (Source.starImage H K).Normal :=
    Subgroup.Normal.map (inferInstance : (K.subgroupOf H).Normal)
      (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let _ := VH_commutative_of_global_span G₁ H V hH.2.1
  have hne : V₃ ≠ ⊥ := fun hz => hline (le_bot_iff.mp (h13.trans hz.le))
  have hgen := original_V_generated L T V V₁ V₃ n hfixed h3V hne
  have hUP := (hcores H hH).trans (pCoreIn_le 2 (L ⊔ T))
  have hseed := (UH_barKernel_commutator L H K T V V₁ V₃ n hCT hTH h13 h3V
    ρ s hker eK E he hmark).trans h3V
  let hnormal := V_normal_in_UL L H V V₃ h3V hgen
  let _ := hnormal
  let helem := ULsection_elementary_of_UH L H T V V₃ h3V n.normalizes_V hUP hseed
  let _ := helem
  let hULnorm := LT_normalizes_UL L H T V₃ hTH n.normalizes_L
  let _ := barKernel_normal (L ⊔ T) V n.normalizes_V
  obtain ⟨τ, hτ⟩ := exists_section_representation (L ⊔ T) (Source.UL L H V₃) V
    (barKernel (L ⊔ T) V) hULnorm n.normalizes_V
    (UL_barKernel_commutator_of_UH L H T V V₃ n.normalizes_V hUP hseed)
  obtain ⟨σ, hσ⟩ := bar_action_on_image (L ⊔ T) (Source.UL L H V₃) V
    hULnorm n.normalizes_V τ hτ
  have hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G) :=
    ((Source.K2_le_centralizer H V₂).trans inf_le_right).trans
      ((centralizer_le_normalizer _).trans
        (TransvectionParabolic.local_normality I₂ L₂ _ V₂ hI hres))
  exact ⟨{
    contains := V_le_UL L H V V₃ hgen
    normal := hnormal
    elementary := helem
    normalizes_UL := hULnorm
    normalizes_V := n.normalizes_V
    normalizes_UH := L1T_normalizes_UH H T L₁ V₃ (le_sup_left.trans hH.1.2) hTH
    normalizes_U2 := L2T_normalizes_U2 H T L₂ V V₂ hTH hT₂
      (le_sup_right.trans n.normalizes_V) ((hL₂.trans le_sup_left).trans n.normalizes_V) hKL
    kernel_commutator := UL_barKernel_commutator_of_UH L H T V V₃ n.normalizes_V hUP hseed
    action := σ
    conjugation := hσ }⟩

/-- The kernel bound in ambient centralizer notation. -/
theorem Data.ambient_kernel_commutator {L H T L₁ L₂ V V₂ V₃ : Subgroup G}
    (d : Data L H T L₁ L₂ V V₂ V₃) :
    ⁅Source.UL L H V₃, (L ⊔ T) ⊓ centralizer (V : Set G)⁆ ≤ V := by
  simpa only [barKernel_map] using d.kernel_commutator

/-- Use the given actual bar-image isomorphism with S₆. The formula retains
the canonical map from LT to that very image. -/
theorem Data.exists_symmetric_action {L H T L₁ L₂ V V₂ V₃ : Subgroup G}
    (d : Data L H T L₁ L₂ V V₂ V₃)
    (e : (barMap (L ⊔ T) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    let _ := d.normal
    let _ := d.elementary
    ∃ ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (Source.ULsection L H V₃ V)),
      SectionConjugationAlong (L ⊔ T) (Source.UL L H V₃) V
        (e.toMonoidHom.comp (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)
        d.normalizes_UL ρ := by
  let _ := d.normal
  let _ := d.elementary
  refine ⟨d.action.comp e.symm.toMonoidHom, ?_⟩
  intro p b
  change d.action (e.symm (e ((barMap (L ⊔ T) V d.normalizes_V).rangeRestrict p))) _ = _
  rw [e.symm_apply_apply]
  exact d.conjugation p b

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.SectionStructure

end
