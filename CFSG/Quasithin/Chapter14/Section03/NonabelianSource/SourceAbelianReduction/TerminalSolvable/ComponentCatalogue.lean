module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import Theory.GroupTheory.CComponent.NormalFromNontrivialImage

/-!
# Transporting the actual component catalogue

The image rows below retain concrete group isomorphisms and normality of the
actual dotted component. Normality lifts to the point normalizer because a
nontrivial normal image detects normality of a C-component. Consequently the
original component equals its T-conjugate span, even when the terminal action
kernel is not solvable.

In the small-actor branch, original 14.3.12 identifies the terminal kernel
with O₂(H). Subnormality then identifies its intersection with the lifted
component with that component's intrinsic two-core. The first isomorphism
theorem transports each of the four large dotted rows to the literal
two-core quotient required by the empty-family sieve.

This module proves transport, not exhaustiveness of the image rows. The
marked and exchanged constituent recognition and the complementary
large-actor branch remain separate mathematical obligations.

Source: Aschbacher--Smith 14.3.12--15, printed pp.993--994; G.10.15 and G.11.2,
printed pp.361--367.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open scoped IsMulCommutative

/-- The four large rows on the actual dotted component. These are image
isomorphisms; identifying the intrinsic two-core quotient is a separate step. -/
def ExcludedComponentImage {D : Type*} [Group D] (L : Subgroup D) : Prop :=
  Nonempty (L ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∨
  Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
  Nonempty (L ≃* Sporadic.Mathieu.M22) ∨
  Nonempty (L ≃* Sporadic.Mathieu.M22TripleCover)

/-- The small rows include a component exchanged with a conjugate. -/
def SmallComponentImage {D : Type*} [Group D] (L : Subgroup D) : Prop :=
  Nonempty (L ≃* alternatingGroup (Fin 5)) ∨
  Nonempty (L ≃* alternatingGroup (Fin 6))

/-- The precise dotted-image recognition output, including the normality
needed outside the small rows. This definition asserts no classification. -/
def ComponentImageCases {D : Type*} [Group D] (L : Subgroup D) : Prop :=
  (L.Normal ∧ ExcludedComponentImage L) ∨ SmallComponentImage L ∨
  (L.Normal ∧ Nonempty (L ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- Only the kernel on the actual lifted component needs to be identified.
The ambient terminal kernel may be larger than O₂(H). -/
def ComponentLift.twoCoreQuotientEquivDot_of_restricted_kernel
    {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K)
    (hk : F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
      pCore 2 (K.subgroupOf F.H)) :
    (K ⧸ pCore 2 K) ≃* F.terminalDot K := by
  let a := (subgroupOfEquivOfLe hK.le_pointNormalizer).symm
  let f := (QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap (K.subgroupOf F.H)
  have hf : f.ker = pCore 2 (K.subgroupOf F.H) := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact hk
  exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    ((QuotientGroup.quotientMulEquivOfEq hf.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f
        ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap_surjective _)))

/-- The actual quotient isomorphism when the terminal action kernel is O₂(H).
Subnormality identifies its restriction with the intrinsic two-core. -/
def ComponentLift.twoCoreQuotientEquivDot
    {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K)
    (hk : F.terminalHatAction.ker = pCore 2 F.H) :
    (K ⧸ pCore 2 K) ≃* F.terminalDot K :=
  hK.twoCoreQuotientEquivDot_of_restricted_kernel
    (by rw [hk]; exact (pCore_subnormal_eq_comap 2 hK.component.subnormal).symm)

/-- A normal dotted component is already its original T-conjugate span.
No assumption on the whole terminal action kernel is needed. -/
theorem ComponentLift.eq_conjugateSpanBy_of_image_normal
    {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hn : (F.terminalDot K).Normal) :
    K = conjugateSpanBy K (T : Subgroup G) := by
  have hne : F.terminalDot K ≠ ⊥ := by
    intro hb
    exact hK.image_moved (by rw [hb, commutator_bot_left])
  have hnormal : (K.subgroupOf F.H).Normal :=
    hK.component.normal_of_normal_nontrivial_image
      (QuotientGroup.mk' F.terminalHatAction.ker) hn hne
  have hnorm : F.H ≤ normalizer K :=
    (normal_subgroupOf_iff_le_normalizer hK.le_pointNormalizer).mp hnormal
  exact le_antisymm (le_conjugateSpanBy _ _)
    (conjugateSpanBy_le le_rfl ((F.invariant 1).trans hnorm))

/-- Transport all dotted rows along an actual two-core quotient isomorphism. -/
theorem ComponentLift.cases_of_image_cases
    {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K)
    (e : (K ⧸ pCore 2 K) ≃* F.terminalDot K)
    (hc : ComponentImageCases (F.terminalDot K)) : ComponentCases F K := by
  rcases hc with ⟨hn, hlarge⟩ | hsmall | ⟨hn, h8⟩
  · refine Or.inl ⟨hK.eq_conjugateSpanBy_of_image_normal hn, ?_⟩
    rcases hlarge with ha | ha | ha | ha
    · exact Or.inl (ha.map e.trans)
    · exact Or.inr (Or.inl (ha.map e.trans))
    · exact Or.inr (Or.inr (Or.inl (ha.map e.trans)))
    · exact Or.inr (Or.inr (Or.inr (ha.map e.trans)))
  · exact Or.inr (Or.inl hsmall)
  · exact Or.inr (Or.inr ⟨hK.eq_conjugateSpanBy_of_image_normal hn, h8⟩)

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Actual small-actor application: original 14.3.12 discharges the kernel
comparison, so only dotted-image recognition remains explicit. -/
theorem source_component_cases_of_small_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (hc : ComponentImageCases (F.terminalDot K)) : ComponentCases F K := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d hne hgP hgH hyp hm).2.2.2.2
  exact hK.cases_of_image_cases (hK.twoCoreQuotientEquivDot hk) hc

/-- Lift one recognized moved dotted component in the small-actor branch.
Image recognition remains an explicit upstream premise; the ambient local
lift, quotient comparison and conjugate-span clauses are all discharged. -/
theorem source_component_catalogue_of_small_actor_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hmove : ⁅L, F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hc : ComponentImageCases L) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  obtain ⟨K, hKH, hlocal, hcomp, he, _, hnormal⟩ :=
    Recognition.terminal_component_lift hG F (by decide) L hL
  change F.terminalDot K = L at he
  have hK : ComponentLift F g K :=
    ⟨hKH, hlocal, hcomp, he.symm ▸ hL, he.symm ▸ hmove, hnormal⟩
  exact ⟨K, hK, source_component_cases_of_small_actor hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp hm hK (he.symm ▸ hc)⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
