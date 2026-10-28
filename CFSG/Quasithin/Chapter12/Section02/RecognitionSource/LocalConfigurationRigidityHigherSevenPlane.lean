module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherComponentExclusions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.Representation.NaturalSevenPlaneDegree

/-!
# Excluding the natural seven-plane containing image in 12.2.25

The original radical R=C_T(U) is self-centralizing: its Sylow centralizer
is itself, and the source characteristic-two hypothesis upgrades this to
C_G(R)=R. Thus the literal quotient N_G(R)/R acts faithfully on R. The
previous centralizer splitting bounds its binary dimension by nine.

A subgroup of this quotient with a normal seven-plane and natural SL₂(7)
quotient would instead require binary degree at least twenty-four. The
lower-layer proof constructs the actual quaternion conjugations from that
natural-action marking. This rules out the natural-action row of A.3.6
for the containing image and applies immediately to the existing binary
rigidity/parabolic consumer. The containing-image catalogue, centerless
smaller-image identification and marked A₇ recognition remain with
qt-d-12213-local-rigidity; no unconditional residual normality is asserted.

Source: Aschbacher–Smith, original 12.2.25, printed p.805, and A.3.6(3),
printed p.43. The extension notation SL₂(7)/E₄₉ retains its normal kernel
and its literal conjugation action; no splitting is required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Self-centralization holds before residual normality, in every source dimension. -/
theorem sectionRadical_selfCentralizing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    centralizer (sectionRadical T U : Set G) = sectionRadical T U := by
  let R := sectionRadical T U
  let : IsElementaryAbelian 2 R := B.elementary
  let : IsElementaryAbelian 2 U := C.elementary
  have hUR : U ≤ R := le_inf C.core_le_sylow (le_centralizer U)
  have hne : R ≠ ⊥ := ne_bot_of_le_ne_bot (C.core_ne_bot (by have := A.dimension.1; omega)) hUR
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := sylow_normalizes_sectionRadical C
  have hRC : R ≤ centralizer (R : Set G) := le_centralizer R
  have he : (T : Subgroup G) ⊓ centralizer (R : Set G) = R :=
    le_antisymm (inf_le_inf_left _ (centralizer_le hUR)) (le_inf inf_le_left hRC)
  have hN : normalizer (R : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
      ⟨R, hne, T.isPGroup'.to_le inf_le_left, rfl⟩ hTR
  have hCN : centralizer (R : Set G) ≤ normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hC : centralizer (R : Set G) ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hN (ne_bot_of_le_ne_bot hne hRC) hCN
      (normal_subgroupOf_centralizer_normalizer (R : Set G)).isSubnormal
  have hcoreT : (normalizer (R : Set G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTR] using
      pCoreIn_le_sylow (normalizer (R : Set G)) (T.subtype hTR)
  have hcoreR : (centralizer (R : Set G)).pCoreIn 2 ≤ R := by
    apply (le_inf ?_ (pCoreIn_le 2 _)).trans he.le
    exact (pCoreIn_mono_of_normalizes hCN (normalizer_le_normalizer_centralizer R)).trans hcoreT
  exact le_antisymm
    ((le_inf le_rfl (centralizer_le hcoreR)).trans (hC.trans hcoreR)) hRC

/-- The actual elementary radical has binary dimension at most nine. -/
theorem sectionRadical_finrank_le_nine
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    letI : IsElementaryAbelian 2 (sectionRadical T U) :=
      (RigidityKernel.source_centralizers h D structural A C hnone).elementary
    Module.finrank (ZMod 2) (Additive (sectionRadical T U)) ≤ 9 := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  let : IsElementaryAbelian 2 (sectionRadical T U) := B.elementary
  have hc := source_radical_card_bound h D structural A C hnone
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (sectionRadical T U))
  change Nat.card (sectionRadical T U) = _ at he
  rw [Nat.card_zmod] at he
  have hb : 2 * (d-1) + 1 ≤ 9 := by have := A.dimension.2; omega
  have hp : 2 ^ Module.finrank (ZMod 2) (Additive (sectionRadical T U)) ≤ 2^9 :=
    he.symm.trans_le (hc.trans (Nat.pow_le_pow_right (by decide) hb))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp

/-- No subgroup of the literal radical quotient has the natural seven-plane action. -/
theorem sectionRadical_quotient_no_natural_seven_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (K : Subgroup (NormalizerQuotient (sectionRadical T U)))
    (N : Subgroup K) [N.Normal] :
    ¬ Chapter1.Section02.LocalModels.NaturalSL2Action K N 7 := by
  intro hm
  obtain ⟨F,_,_,hF,v,ρ,hv⟩ := hm
  let R := sectionRadical T U
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  let : IsElementaryAbelian 2 R := B.elementary
  have he := sectionRadical_selfCentralizing h A C B
  let a := (action R he.symm.le).comp K.subtype
  have ha : Function.Injective a := (action_injective R he).comp K.subtype_injective
  let σ := Representation.elementaryRepresentation (p := 2) a
  have hσ : Function.Injective σ := by
    intro x y hxy
    apply ha
    apply MulEquiv.ext
    intro r
    exact congrArg Additive.toMul (congrArg
      (fun f : Module.End (ZMod 2) (Additive R) => f (Additive.ofMul r)) hxy)
  have hlarge := Representation.NaturalSevenPlaneDegree.finrank_ge N hF v ρ hv σ hσ
  have hsmall := sectionRadical_finrank_le_nine h D structural A C hnone
  change Module.finrank (ZMod 2) (Additive R) ≤ 9 at hsmall
  omega

/-- The original normal containing component, retaining both previous exclusions
and the exclusion of every literal natural seven-plane kernel. -/
theorem source_containing_component_seven_sieve
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V ≤ K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      (∀ (N : Subgroup (ThreeRigidity.image T U K)) [N.Normal],
        ¬ Chapter1.Section02.LocalModels.NaturalSL2Action (ThreeRigidity.image T U K) N 7) ∧
      (rigidityHyperplaneResidual L U V ≠ K →
        (∀ m, (m = 3 ∨ m = 4 ∨ m = 5) →
          ¬ ClassicalGroup.IsPSL (ThreeRigidity.image T U K) m 2) ∧
        ¬ (Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 5 ∨
          Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 6 ∨
          Chapter1.Section02.LocalModels.IsAlternatingCover (ThreeRigidity.image T U K) 6)) := by
  obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hex⟩ :=
    source_containing_component_sieve h D structural A C hnone hd
  exact ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,
    fun N _ => sectionRadical_quotient_no_natural_seven_plane h D structural A C hnone
      (ThreeRigidity.image T U K) N,hex⟩

/-- Discharge the natural seven-plane alternative at the existing rigidity
consumer. The containing-image catalogue and the exceptional A₇ row remain
with this task's final assembly. -/
theorem source_rigidity_of_binary_or_seven_plane_containing_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (hmodel : (∃ m, (m = 3 ∨ m = 4 ∨ m = 5) ∧
        ClassicalGroup.IsPSL (ThreeRigidity.image T U K) m 2) ∨
      ∃ N : Subgroup (ThreeRigidity.image T U K), ∃ _ : N.Normal,
        Chapter1.Section02.LocalModels.NaturalSL2Action (ThreeRigidity.image T U K) N 7) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U := by
  rcases hmodel with ⟨m,hm,hmodel⟩ | ⟨N,hN,hmodel⟩
  · exact source_rigidity_of_binary_linear_containing_image h D structural A C hnone hd
      hKN hK hYK hn hm hmodel
  · exact (sectionRadical_quotient_no_natural_seven_plane h D structural A C hnone
      (ThreeRigidity.image T U K) N hmodel).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
