module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Preparation
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient
public import Theory.GroupTheory.OddInvertedSubgroups

/-!
# The original involution on the odd cores in 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The fixed line supplies the same involution z for U and all its planes.
Their literal common Sylow subgroup C_T(V), together with even
characteristic and maximality of N_G(V) = C_G(z), verifies every hypothesis
of 1.1.6. The proved 1.1.5(2) then inverts their embedded odd cores, which
are consequently abelian. No inversion or component classification is an input.

Source: Aschbacher–Smith, 12.4.8, printed pp.815–816, using 1.1.5–6.
-/

@[expose] public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
open Section02 SmallFusion ChapterE ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- O(C_G(W)), included in the original ambient group. -/
def core (W : Subgroup G) : Subgroup G :=
  (pPrimeCore 2 (centralizer (W : Set G))).map (centralizer (W : Set G)).subtype

theorem core_odd (W : Subgroup G) : Nat.Coprime 2 (Nat.card (core W)) := by
  rw [core, ← Nat.card_congr ((pPrimeCore 2 (centralizer (W : Set G))).equivMapOfInjective
    (centralizer (W : Set G)).subtype Subtype.val_injective).toEquiv]
  exact pPrimeCore_coprime_card

omit [Finite G] in
theorem core_ne_bot_iff (W : Subgroup G) :
    core W ≠ ⊥ ↔ pPrimeCore 2 (centralizer (W : Set G)) ≠ ⊥ := by
  exact ((pPrimeCore 2 (centralizer (W : Set G))).map_eq_bot_iff_of_injective
    (centralizer (W : Set G)).subtype_injective).not

/-- The fixed involution and the literal equality M = C_G(z). -/
theorem fixed_involution (c : Configuration T L V U) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      normalizer (V : Set G) = centralizer ({z} : Set G) := by
  obtain ⟨z, hz, hfix, hM, hMV, _, _⟩ :=
    fixed_involution_setup_of_card_two c.hypothesis c.chosen c.structural
      (c.extension.fixed_card_eq_two c.fixed_nontrivial)
  exact ⟨z, hz, hfix, hMV.symm.trans hM⟩

/-- Construct the genuine 1.1.5 hypotheses for any of the actual subspace
centralizers having the common Sylow image. -/
theorem marked_centralizer (c : Configuration T L V U)
    (z : G) (hz : orderOf z = 2) (hfix : fixedSubgroup L V = zpowers z)
    (hM : normalizer (V : Set G) = centralizer ({z} : Set G))
    (W : Subgroup G) (hWV : W ≤ V) (hW : W ≠ ⊥)
    (hS : Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (W : Set G))) :
    ∃ S : Sylow 2 (centralizer (W : Set G)),
      (S : Subgroup (centralizer (W : Set G))).map (centralizer (W : Set G)).subtype =
        sylowCentralizer (T : Subgroup G) V ∧
      Chapter1.Lemma115Hypotheses (centralizer (W : Set G)) S
        (normalizer (V : Set G)) z := by
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  obtain ⟨S, hS⟩ := hS
  have hE := source_hypothesisE61 c.hypothesis c.structural
    c.extension c.fixed_nontrivial
  have hzV : z ∈ V := (show fixedSubgroup L V ≤ V from inf_le_left)
    (hfix.symm ▸ mem_zpowers z)
  refine ⟨S, hS, ?_⟩
  refine Chapter1.lemma_1_1_6 hW (IsElementaryAbelian.isPGroup 2 W)
    (le_centralizer W) le_rfl (Subgroup.centralizer_le_normalizer _) S T
    (hS ▸ (show sylowCentralizer (T : Subgroup G) V ≤ T from inf_le_left))
    hz (c.chosen.le_sylow hzV) ?_ hE.maximalTwoLocal hM.ge ?_
  · intro t ht
    exact mem_centralizer_singleton_iff.mp (hM ▸ hE.sylow_le ht)
  · intro N hN hTN
    exact Chapter1.mem_He_iff.mpr (c.hypothesis.simpleQTKE.evenCharacteristic T N hN hTN)

/-- Source 1.1.5(2) on the embedded odd core, preserving z and the subtype map. -/
theorem inverts_core (c : Configuration T L V U)
    (z : G) (hz : orderOf z = 2) (hfix : fixedSubgroup L V = zpowers z)
    (hM : normalizer (V : Set G) = centralizer ({z} : Set G))
    (W : Subgroup G) (hWV : W ≤ V) (hW : W ≠ ⊥)
    (hS : Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (W : Set G))) :
    ∀ x ∈ core W, z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨S, _, h⟩ := marked_centralizer c z hz hfix hM W hWV hW hS
  rintro x ⟨y, hy, rfl⟩
  exact h.inverts_oddCore y hy

/-- The simultaneous inversion and abelianness needed at the start of the
odd-core branch of 12.4.8, for U and every hyperplane U₀ of U. -/
theorem simultaneous_inversion (c : Configuration T L V U) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      normalizer (V : Set G) = centralizer ({z} : Set G) ∧
      (∀ x ∈ core U, z * x * z⁻¹ = x⁻¹) ∧ IsMulCommutative (core U) ∧
      ∀ W ≤ U, subgroupCorank U W = 1 →
        (∀ x ∈ core W, z * x * z⁻¹ = x⁻¹) ∧ IsMulCommutative (core W) := by
  obtain ⟨z, hz, hfix, hM⟩ := fixed_involution c
  have hg := escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape
  have hU : U ≠ ⊥ := hg.2.2.2.1.2.1
  have hi := inverts_core c z hz hfix hM U c.le_module hU c.sylow_centralizers.1
  refine ⟨z, hz, hfix, hM, hi, isMulCommutative_of_inverted _ z hi, ?_⟩
  intro W hWU hcor
  have hW : W ≠ ⊥ := (hg.2.2.2.2 W hWU hcor).2.2.2.2.1
  have hiW := inverts_core c z hz hfix hM W (hWU.trans c.le_module) hW
    (c.sylow_centralizers.2 W hWU hcor)
  exact ⟨hiW, isMulCommutative_of_inverted _ z hiW⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
