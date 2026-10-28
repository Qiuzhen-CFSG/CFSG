module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ReflectionOrbit
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Actual A₆ model inputs for the terminal construction

The four adapters discharge every finite-model premise of the terminal E₁₆
construction. The marked Sylow model supplies the normal cyclic-four and
centralizer geometry, with the actual permutation-induced transposition.
The four-group normalizers supply fusion, coboundaries, outer generation,
and the reflection orbit. All maps retain the actual inner A₆ embedding.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.569–570, following Lemma 2.5.27.
This module supplies model calculations; the source Frattini, rank-one and
centralizer conclusions remain obligations of the chapter assembly.
-/

public section

namespace CFSG.Quasithin.Chapter2.A6Shadow

open Subgroup A6ShadowConstruction
open AlternatingSix.ShadowLocal

/-- Normalizer transitivity and the actual coboundary conjugator. -/
theorem fusionModelFacts : SquareMembership.Fusion.ModelFacts where
  four_transitive := four_transitive
  outside_coboundary := outside_coboundary

/-- The S₄ normalizer and its outer automorphism complement. -/
theorem actionNormalizerModelFacts : ActionNormalizer.ModelFacts where
  symmetric F hF := by
    let := hF
    exact four_normalizer_equiv_symmetric F
  outer_generates F hF a _ ha haF b hbF := by
    let := hF
    exact FourNormalizers.outer_normalizer_generates F a ha haF b hbF

/-- Conjugate the reflection inside the specified actual Sylow subgroup. -/
theorem reflectionOrbit (P : Sylow 2 AutA6) : FourGroupChoice.ReflectionOrbit P := by
  intro F hF hFD b hbP _ hbC hbD
  let := hF
  exact four_normalizer_reflection_orbit P F hFD b hbP hbC hbD

open Identification SylowGeometry

private theorem inner_image (P : Sylow 2 AutA6) :
    (sylowInner P).map (P : Subgroup AutA6).subtype = CoreReduction.innerSylow P := by
  ext b
  exact ⟨fun ⟨s, hs, he⟩ => he ▸ ⟨s.property, hs⟩,
    fun hb => ⟨⟨b, hb.1⟩, hb.2, rfl⟩⟩

private theorem centralizer_singleton_zpowers {B : Type*} [Group B] (u : B) :
    centralizer ({u} : Set B) = centralizer (zpowers u : Set B) := by
  ext b
  constructor
  · intro hb v hv
    obtain ⟨n, rfl⟩ := hv
    exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp hb) n).symm
  · intro hb
    exact mem_centralizer_singleton_iff.mpr (hb u (mem_zpowers u)).symm

/-- All core-reduction model premises, transported from the marked Sylow model. -/
noncomputable def coreModelGeometry (P : Sylow 2 AutA6) : CoreReduction.ModelGeometry P := by
  let t : P := sylowEquiv P Holomorph.transposition
  let π := (P : Subgroup AutA6).subtype
  have hT : transpositionSubgroup P = zpowers t := sylowEquiv_transpositionSubgroup P
  have ht2 : t ^ 2 = 1 := by
    change (sylowEquiv P Holomorph.transposition) ^ 2 = 1
    rw [← map_pow, show Holomorph.transposition ^ 2 = 1 by decide +kernel, map_one]
  have htC : t ∈ centralizer (sylowInner P : Set P) := by
    rw [centralizer_inner, hT]
    exact mem_sup_right (mem_zpowers t)
  have hCt : centralizer ({t} : Set P) = transpositionSubgroup P ⊔ sylowInner P := by
    rw [centralizer_singleton_zpowers, ← hT, centralizer_transposition,
      natural_eq_transposition_sup_inner]
  have hCtmap : (P : Subgroup AutA6) ⊓ centralizer ({(t : AutA6)} : Set AutA6) =
      zpowers (t : AutA6) ⊔ CoreReduction.innerSylow P := by
    rw [← map_subtype_centralizer_singleton, hCt, Subgroup.map_sup, inner_image,
      hT, MonoidHom.map_zpowers]
    rfl
  let eD := Classical.choice (sylowInner_dihedral P)
  let eDI : sylowInner P ≃* CoreReduction.innerSylow P :=
    ((sylowInner P).equivMapOfInjective π (P : Subgroup AutA6).subtype_injective).trans
      (MulEquiv.subgroupCongr (inner_image P))
  refine {
    card := sylow_card P
    dihedral := ⟨eDI.symm.trans eD⟩
    rotation := (cyclicFour P).map π
    rotation_le := ?_
    transposition := t
    is_transposition := ⟨_, conjugatedTransposition_isSwap P, sylowEquiv_transposition P⟩
    transposition_mem := t.property
    transposition_square := congrArg π ht2
    transposition_commutes := ?_
    normal_cyclicFour := ?_
    reflection_rotation := ?_
    involution_centralizer := ?_
    transposition_centralizer := hCtmap
    product := ?_ }
  · rw [← inner_image]
    exact map_mono (cyclicFour_le_inner P)
  · intro b hb
    exact congrArg π (htC (⟨b, hb.1⟩ : P) hb.2)
  · intro N hNP hN hfour
    let := hN
    obtain ⟨e⟩ := hfour
    let eN := (subgroupOfEquivOfLe hNP).trans e
    let : IsCyclic (N.subgroupOf (P : Subgroup AutA6)) := eN.isCyclic.mpr inferInstance
    have hc : Nat.card (N.subgroupOf (P : Subgroup AutA6)) = 4 := by
      rw [Nat.card_congr eN.toEquiv]
      simp
    have he := congrArg (Subgroup.map π) (normal_cyclicFour_sup_transposition P _ hc)
    simpa only [π, Subgroup.map_sup, hT, MonoidHom.map_zpowers,
      map_subgroupOf_eq_of_le hNP, Subgroup.subtype_apply] using he
  · intro a ha ha2 haZ y hy
    let u : P := ⟨a, ha.1⟩
    have huD : u ∈ sylowInner P := ha.2
    have hu2 : u ^ 2 = 1 := Subtype.ext ha2
    have huZ : u ∉ center P := by
      intro hu
      apply haZ
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      change (⟨a, ha⟩ : CoreReduction.innerSylow P) ∈ center (CoreReduction.innerSylow P)
      rw [mem_center_iff]
      intro b
      apply Subtype.ext
      exact congrArg π (mem_center_iff.mp hu (⟨b, b.property.1⟩ : P))
    obtain ⟨v, hv, rfl⟩ := hy
    have he := inner_involution_inverts_normal_cyclicFour P (cyclicFour P)
      (cyclicFour_card P) u huD huZ hu2 v hv
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha2)
    simpa only [map_mul, map_inv, π, u, Subgroup.subtype_apply, hai] using congrArg π he
  · intro a ha ha2 haC haD
    let u : P := ⟨a, ha⟩
    have huC : u ∈ centralizer (sylowInner P : Set P) := by
      intro b hb
      exact Subtype.ext (haC b ⟨b.property, hb⟩)
    have huZ : u ∉ center P := by
      intro hu
      apply haD
      refine ⟨ha, ?_⟩
      rw [center_eq] at hu
      have hle : center P ≤ sylowInner P := by
        rw [center_eq, ← sylowEquiv_innerD]
        apply zpowers_le.mpr
        rw [mem_map_equiv]
        simp only [MulEquiv.symm_apply_apply]
        rw [show 4 = 2 * 2 from rfl, pow_mul]
        exact Subgroup.pow_mem _ (subset_closure (by simp)) _
      exact hle ((center_eq P).symm ▸ hu)
    have he := congrArg (Subgroup.map π)
      (centralizer_innerCentralizer_involution P u huC huZ (Subtype.ext ha2))
    rw [hT, ← centralizer_singleton_zpowers] at he
    change (centralizer ({u} : Set P)).map (P : Subgroup AutA6).subtype =
      (centralizer ({t} : Set P)).map (P : Subgroup AutA6).subtype at he
    rw [map_subtype_centralizer_singleton (P : Subgroup AutA6) u,
      map_subtype_centralizer_singleton (P : Subgroup AutA6) t] at he
    exact he
  · let ec : centralizer ({t} : Set P) ≃* centralizer (transpositionSubgroup P : Set P) :=
      MulEquiv.subgroupCongr (by rw [hT, centralizer_singleton_zpowers])
    let em := (centralizer ({t} : Set P)).equivMapOfInjective π
      (P : Subgroup AutA6).subtype_injective
    have hm : (centralizer ({t} : Set P)).map π =
        zpowers (t : AutA6) ⊔ CoreReduction.innerSylow P :=
      (map_subtype_centralizer_singleton _ t).trans hCtmap
    exact ⟨(MulEquiv.subgroupCongr hm.symm).trans
      (em.symm.trans (ec.trans (centralizerTranspositionEquiv P)))⟩

end CFSG.Quasithin.Chapter2.A6Shadow
