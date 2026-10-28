module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SelectedEndpoint.NaturalDual
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.FixedFactor
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SourceBounds
public import Theory.Representation.BinaryConjugationSection.Join
public import Theory.Representation.BinaryConjugationSection.EmbeddedSection

/-!
# The critical crossing from the original separate natural and dual sections

The common-kernel join construction supplies both literal combined sections
on the same coordinates. The natural action has exactly the original
O₂(Mc) kernel; the fixed factor is the canonical commutator preimage. The
component's full image places a suitable restriction in the generalized
Fitting preimage. These constructions discharge the joined-section, kernel,
support-label and fixed-factor premises of the selected-endpoint theorem.

The whole-module automorphism embedding is constructed in
`SingleComponent/Marking`. The original single-component and paired-support
inputs remain the earlier-source obligations; final suitable-choice assembly
belongs to qt-e-suitable-existence. This is not unconditional 14.6.24.

Source: Aschbacher--Smith, 14.6.22--24(4), printed pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The natural action on a paired decomposition has exactly the original
core as kernel, not merely a two-group kernel. -/
theorem natural_kernel_eq_core_of_dual_decomposition
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (W W' C : Subgroup G) (hWU : W ≤ D.UH)
    (f : (D.H ⊓ normalizer (W : Set G) : Subgroup G) →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (c : BinaryConjugationSection (D.H ⊓ normalizer (W : Set G)) W D.V₁
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (c' : BinaryConjugationSection (D.H ⊓ normalizer (W : Set G)) W' D.V₁
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)))
    (hcover : ∀ v ∈ D.UH, ∃ w ∈ W, ∃ w' ∈ W', ∃ v₀ ∈ C, v = w*w'*v₀)
    (hfixed : ∀ x ∈ D.H, ∀ v₀ ∈ C, ⁅v₀,x⁆ ∈ D.V₁) :
    f.ker = D.QH.subgroupOf (D.H ⊓ normalizer (W : Set G)) := by
  apply le_antisymm
  · exact natural_kernel_le_core_of_dual_decomposition h W W' C f c c' hcover hfixed
  · intro x hx
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,hw⟩ := c.onto (Multiplicative.ofAdd v)
    have he := (c.fixed_coordinate_iff_commutator_mem x w).mpr
      (h.commutator_UH_QH_le_point (commutator_mem_commutator (hWU w.property) hx))
    change f x (c.coordinates w).toAdd = (c.coordinates w).toAdd at he
    rw [hw] at he
    exact he

namespace SelectedEndpoint
open Chapter13.Section08
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (sectionModel : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ)
    (ι : Source.Hstar Mc →* MulAut BinaryLinearThree.Group) (hι : Function.Injective ι)
    (embedding : BinaryLinearThree.NaturalDual.Space →ₗ[ZMod 2] E)
    (hembedding : Function.Injective embedding)
    (hact : ∀ a v, ρ a (embedding v) = embedding (BinaryLinearThree.NaturalDual.autAction (ι a) v))
    (W W' : Subgroup G)

local notation "U" => conjugateSpanBy (localModule T M) Mc
local notation "Z" => centralInvolutions T
local notation "L" => (Mc ⊓ normalizer (W : Set G) : Subgroup G)
local notation "h" => ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab

include sectionModel hι embedding hembedding hact in
/-- Construct both joined section markings, their shared coordinates and exact
kernel from the original natural and dual sections. The fixed factor is the
canonical commutator preimage, and the component supplies the required full
image inside the generalized Fitting preimage. -/
theorem source_crossing_of_paired_sections
    (hL : (L).subgroupOf Mc = (MulAut.innerSubgroup BinaryLinearThree.Group).comap
      (ι.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (f : (L) →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection (L) W Z
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (cdual : BinaryConjugationSection (L) W' Z
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)))
    (hWU : W ≤ U) (hW'U : W' ≤ U) (hsep : W ⊓ W' ≤ Z)
    (hB : ⁅U,Mc⁆ ≤ W ⊔ W')
    (K : Subgroup G)
    (hKres : (solvableResidual Mc).map Mc.subtype = K)
    (hK : (K.subgroupOf Mc).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL)
    (hKW : K ≤ normalizer (W : Set G))
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W) (hu : ComponentSupports.Suitable (h) Mc u) :
    ∃ i : (h).CriticalEndpoint, ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (i.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ q : SourceCrossingGeometry (localModule T M) Mc Mc u,
        q.A = U ∧ q.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
  let hh := h
  let B := W ⊔ W'
  let C := commutatorPreimage U Mc Z
  obtain ⟨_,_,_,hfixed,hcover⟩ := source_fixed_factor_of_pair_commutator
    hG T hempty hM hunique hmany hcard e hab W W' hWU hW'U hsep f hf c cdual hB
  have hker := natural_kernel_eq_core_of_dual_decomposition hh W W' C hWU
    f c cdual hcover hfixed
  have hcomm : W ≤ centralizer (W' : Set G) :=
    hWU.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hW'U))
  obtain ⟨dL,hdL,hW,hW'⟩ := c.exists_join_section cdual hcomm hsep
  let fSL := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp f
  have hfSL : Function.Surjective fSL :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp hf
  obtain ⟨hKL,_,hKF,hfull⟩ := source_component_action_placement
    hG T hempty hM hunique hmany hcard e K W hKres hK eK hKW fSL hfSL
  let J := K ⊔ B
  have hBL : B ≤ L := sup_le c.section_le cdual.section_le
  have hJL : J ≤ L := sup_le hKL hBL
  have hJF : J ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc := by
    apply sup_le hKF
    exact (sup_le hWU hW'U).trans (hh.UH_le_QH.trans
      (ChapterA.Section04.twoCore_le_fittingPreimage Mc))
  let φ : J →* BinaryLinear.GL (Fin 3 → ZMod 2) := f.comp (inclusion hJL)
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨k,hk⟩ := hfull ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm a)
    refine ⟨⟨k,show (k:G) ∈ J from (show K ≤ J from le_sup_left) k.property⟩,?_⟩
    apply (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.injective
    exact hk
  have hrep : Representation.prod (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)) =
      naturalDualRepresentation.comp f := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro v
    change _ = naturalDualRepresentation (f a) v
    rw [naturalDualRepresentation_apply]
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro w
      change v.2 (f a⁻¹ w) = v.2 ((f a)⁻¹ w)
      rw [map_inv]
  let dL' : BinaryConjugationSection (L) B Z (naturalDualRepresentation.comp f) :=
    { dL with equivariant := by intro a b; rw [←hrep]; exact dL.equivariant a b }
  let cd : BinaryConjugationSection (L) W' Z (LowRankProfiles.natural.dual.comp f) :=
    { cdual with
      equivariant := by
        intro a b
        have he := cdual.equivariant a b
        change _ = LowRankProfiles.natural.dual (f a) _
        rw [he]
        apply LinearMap.ext
        intro w
        change (cdual.coordinates b).toAdd (f a⁻¹ w) =
          (cdual.coordinates b).toAdd ((f a)⁻¹ w)
        rw [map_inv] }

  let d := dL'.restrictActor hJL (show B ≤ J from le_sup_right)
  have hcover' : ∀ v ∈ U, ∃ b ∈ B, ∃ t ∈ C, v = b*t := by
    intro v hv
    obtain ⟨a,ha,b,hb,t,ht,he⟩ := hcover v hv
    exact ⟨a*b,mul_mem_sup ha hb,t,ht,he⟩
  have hfixed' : ⁅Mc,C⁆ ≤ Z := by
    rw [commutator_comm]
    exact commutator_le.mpr (fun a ha b hb => hfixed b hb a ha)
  exact source_crossing_of_marked_single_component hG T hempty hM hunique hmany hcard e hab
    sectionModel ι hι embedding hembedding hact W W' hL f hf hker c cd hWU hW'U
    s hs hsW u huW hu J B C hJF (sup_le hWU hW'U) φ hφ d dL'
    (fun _ => rfl) hW hW' hB hcover' hfixed'

end SelectedEndpoint
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
