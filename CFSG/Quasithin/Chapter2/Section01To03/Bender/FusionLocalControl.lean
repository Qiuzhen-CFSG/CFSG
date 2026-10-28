module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.AlperinGoldschmidtFusion
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FusionLocalControl.Selected

/-!
# Fusion and local control in the Bender reduction

The literal Alperin–Goldschmidt family controls element fusion without a
fusion-control assumption. If its normalizers lie in M, every normal
two-subgroup of M is strongly closed. Select a minimal normal elementary
abelian subgroup U in the two-core. Maximal two-local uniqueness gives
M = N_G(U) and a nonidentity z in U ∩ Z(T) with C_G(z) ≤ M.

Burnside fusion in the strongly closed abelian subgroup U constructs the
unique z-fixed coset. Normalizer ascent proves (*), and Sylow conjugacy in
element centralizers gives M-control of fusion of all two-elements in M.
All element formulas below use the source's right conjugation g⁻¹ x g.
The canonical left coset action is identified with the source's right coset
action by inversion of representatives.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition 2.2.1 and the recognition-independent
part of Proposition 2.2.2, pp. 518–520. Bender recognition and Lemma 2.2.3's
characteristic-two-local conclusion belong to the parent assembly.
-/

@[expose] public section

open Subgroup
open Theory.GroupTheory

namespace CFSG.Quasithin.Chapter2.BenderFusion

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Definition 2.2.1, with the Sylow image, quotient core, and internal
product all interpreted literally by the generic family definition. -/
abbrev alperinGoldschmidtFamily (T : Sylow 2 G) (D : Subgroup G) : Prop :=
  AlperinGoldschmidt.Family T D

/-- Proposition 2.2.2(1). Normality is relative to M. -/
theorem proposition_2_2_2_one (T : Sylow 2 G) {M U : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hfamily : ∀ D : Subgroup G, alperinGoldschmidtFamily T D →
      normalizer (D : Set G) ≤ M)
    (hUM : U ≤ M) (hMU : M ≤ normalizer (U : Set G)) (hU : IsPGroup 2 U) :
    IsStronglyClosedSet (U : Set G) (T : Subgroup G) ⊤ :=
  AlperinGoldschmidt.normal_p_subgroup_strongly_closed T hTM hfamily hUM hMU hU

/-- The explicitly constructed local data preceding Bender recognition.
Its existence theorem below proves every field from the source hypotheses. -/
structure LocalControlWitness (T : Sylow 2 G) (M : Subgroup G) where
  U : Subgroup G
  ne_bot : U ≠ ⊥
  le_twoCore : U ≤ M.pCoreIn 2
  elementary : IsElementaryAbelian 2 U
  normalizes : M ≤ normalizer (U : Set G)
  normalizer_eq : normalizer (U : Set G) = M
  le_sylow : U ≤ (T : Subgroup G)
  minimal : ∀ W : Subgroup G, W ≤ U → M ≤ normalizer (W : Set G) → W = ⊥ ∨ W = U
  irreducible : ∀ W : Subgroup U,
    (∀ m : M, ∀ a : U, a ∈ W → conjugationAction M U normalizes m a ∈ W) → W = ⊥ ∨ W = ⊤
  strongly_closed : IsStronglyClosedSet (U : Set G) (T : Subgroup G) ⊤
  conjugates_in_M : ∀ x ∈ U,
    {y : G | IsConj x y} ∩ (M : Set G) = {y : G | ∃ m ∈ M, m⁻¹ * x * m = y}
  z : G
  z_mem : z ∈ U
  z_ne_one : z ≠ 1
  z_order : orderOf z = 2
  z_central : ∀ t ∈ (T : Subgroup G), Commute z t
  centralizer_le : centralizer ({z} : Set G) ≤ M
  unique_fixed_coset : ∃! q : G ⧸ M, z • q = q
  source_star : ∀ S : Subgroup G, IsPGroup 2 S → z ∈ S →
    S ≤ M ∧ normalizer (S : Set G) ≤ M
  two_element_fusion : ∀ x y : G, x ∈ M → y ∈ M → IsPGroup 2 (zpowers x) →
    IsConj x y → ∃ m ∈ M, m⁻¹ * x * m = y

/-- Construction of U, z, the unique fixed coset, (*), and two-element fusion
control from the literal family-normalizer hypothesis and two-local uniqueness. -/
theorem exists_local_control (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hfamily : ∀ D : Subgroup G, alperinGoldschmidtFamily T D →
      normalizer (D : Set G) ≤ M) :
    Nonempty (LocalControlWitness T M) := by
  obtain ⟨U, hUne, hUcore, hUe, hMU, hNU, hUT, hmin, z, hzU, hz1, hzc, hCM⟩ :=
    exists_selected_subgroup T M hM hTM hunique
  let _ : IsElementaryAbelian 2 U := hUe
  have hUM : U ≤ M := hUT.trans hTM
  have hc := proposition_2_2_2_one T hTM hfamily hUM hMU
    (IsElementaryAbelian.isPGroup 2 U)
  have hfix := unique_fixed_coset_of_selected T hTM hMU hc hNU.le hzU hCM
  have hclass : ∀ x ∈ U,
      {y : G | IsConj x y} ∩ (M : Set G) = {y : G | ∃ m ∈ M, m⁻¹ * x * m = y} := by
    intro x hx
    ext y
    constructor
    · rintro ⟨hxy, hyM⟩
      obtain ⟨_, m, hm, he⟩ := fusion_into_normal_abelian T hTM hMU hc hNU.le hx hyM hxy
      exact ⟨m⁻¹, M.inv_mem hm, by simpa only [inv_inv] using he⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨isConj_iff.mpr ⟨m⁻¹, by simp only [inv_inv]⟩,
        M.mul_mem (M.mul_mem (M.inv_mem hm) (hUM hx)) hm⟩
  refine ⟨{
    U := U
    ne_bot := hUne
    le_twoCore := hUcore
    elementary := hUe
    normalizes := hMU
    normalizer_eq := hNU
    le_sylow := hUT
    minimal := hmin
    irreducible := conjugationAction_irreducible hMU hmin
    strongly_closed := hc
    conjugates_in_M := hclass
    z := z
    z_mem := hzU
    z_ne_one := hz1
    z_order := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzU) hz1
    z_central := hzc
    centralizer_le := hCM
    unique_fixed_coset := hfix
    source_star := fun S hS hzS =>
      UniqueFixedCoset.p_overgroup_and_normalizer_le (hUM hzU) hfix hS hzS
    two_element_fusion := ?_ }⟩
  intro x y hxM hyM hxp hxy
  obtain ⟨m, hm, he⟩ := UniqueFixedCoset.p_element_fusion T hTM (hUT hzU) hzc hfix
    hxM hyM hxp hxy
  exact ⟨m⁻¹, M.inv_mem hm, by simpa only [inv_inv] using he⟩

/-- The genuine simple-QTKE source setup supplies characteristic two in M
and the complete recognition-independent local-control witness. -/
theorem source_local_control {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hfamily : ∀ D : Subgroup G, alperinGoldschmidtFamily T D →
      normalizer (D : Set G) ≤ M) :
    HasCharacteristicTwo M ∧ Nonempty (LocalControlWitness T M) :=
  ⟨hG.evenCharacteristic T M hM hTM, exists_local_control T M hM hTM hunique hfamily⟩

end CFSG.Quasithin.Chapter2.BenderFusion
