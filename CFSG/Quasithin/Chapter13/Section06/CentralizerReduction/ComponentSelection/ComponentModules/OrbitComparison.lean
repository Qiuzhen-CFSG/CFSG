module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitKernel

/-!
# Comparing both source catalogues in the noninvariant case

The actual quotient map identifies K/O₂(K) with K⁺. Transport the complete
nonnormal-component catalogue through that map and intersect it with the
FF catalogue constructed on the original W_K action. The only surviving
models are SL₂ over an even field of order at least four and PSL₃(2).
Both quotient conventions have the same model and, in the first branch,
the same finite field. No model or classification hypothesis is assumed.

This proves the model comparison in the first sentence of 13.6.14.
The subsequent cubic-diagonal argument must exclude the PSL₃(2) branch
and identify the paired natural action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, printed p.929; 1.2.1(3), p.504; B.5.6, p.105.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ChapterB.QuasisimpleSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem linearTwo_of_binary_projective {X : Type*} [Group X]
    {n : ℕ} (hn : 2 ≤ n) (h : ClassicalGroup.IsPSL X 2 (2 ^ n)) :
    ∃ F : BinaryField, 4 ≤ Nat.card F.Carrier ∧ Nonempty (X ≃* SL(2,F.Carrier)) := by
  obtain ⟨E, hE, hfin, hcard, ⟨e⟩⟩ := h
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let F : BinaryField := {
    Carrier := E
    degree := n
    degree_pos := by omega
    card_eq := hcard }
  refine ⟨F, ?_, ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm⟩⟩
  change 4 ≤ Nat.card E
  rw [hcard]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn

/-- The complete A.3.8/B.5 comparison on the actual intrinsic and plus
quotients, with every classifier input discharged. -/
theorem noninvariant_component_models_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    (∃ F : BinaryField, 4 ≤ Nat.card F.Carrier ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F.Carrier)) ∧
      Nonempty (plusImage K L T z v hL hz K ≃* SL(2,F.Carrier))) ∨
    (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∧
      ClassicalGroup.IsPSL (plusImage K L T z v hL hz K) 3 2) := by
  have hlocal := hG.involution_centralizer_sqtk hv
  have hm := (noninvariant_component_pair_source K L T z v hlocal hK hn).2.1
  let e := componentCoreEquivPlus K L T z v hlocal hL hz hSylow hK hn
  have hplus := hm.of_mulEquiv e.symm
  obtain ⟨hff, hthree⟩ := orbit_plus_ff_model_source hG K L T z v hv hL hz
    hSylow hzOmega hf hK
  let := plusImage_K_quasisimple_source K L T z v hL hz hK hSylow
  rcases intrinsic_model_intersection hplus hff hthree with ⟨n, hn, h⟩ | h
  · obtain ⟨F, hF, ⟨f⟩⟩ := linearTwo_of_binary_projective hn h
    exact Or.inl ⟨F, hF, ⟨e.trans f⟩, ⟨f⟩⟩
  · exact Or.inr ⟨h.of_mulEquiv e, h⟩

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The model comparison under the original 13.6 source hypotheses and
the contrary noninvariance assumption, using the actual hL and hz maps. -/
theorem noninvariant_component_models_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    (∃ F : BinaryField, 4 ≤ Nat.card F.Carrier ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F.Carrier)) ∧
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K ≃* SL(2,F.Carrier))) ∨
    (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∧
      ClassicalGroup.IsPSL (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K) 3 2) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact noninvariant_component_models_source hG K L (T : Subgroup G) _ _
    (marked_orders d.flag.module).2 hL hz
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ (markedZ_mem_Tv_omega d)
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion) hK hn

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
