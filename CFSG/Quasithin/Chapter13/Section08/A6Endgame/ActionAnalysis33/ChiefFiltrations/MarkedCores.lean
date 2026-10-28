module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.ModelDefs
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ChiefCubicCores
import Mathlib.Tactic
/-!
# Cubic conjugation on the marked parabolic and residual cores

The syntheme two-core is the pair-swap cube D; the two-core of its actual
two-residual is the even cube D0. Commutators with the marked pair cycle
put D0 in the residual. Characteristic normality bounds its two-core by
D, and parity then gives exactly D0. The proved pentad outer automorphism
transports these identities to the duad parabolic and its residual K.

All four actual relative centralizer indices are four, hence all four
conjugation cubic lengths are one. The inclusions of residual cores in
parabolic cores add quotients fixed pointwise by the cubic actors. The
outer restrictions are genuine multiplicative equivalences, commute with
these inclusions, and intertwine the actual conjugation actions through
`cubicActorEquiv`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 13.8.33, printed p.968 / PDF p.985. This supplies the canonical model
facts for the source's O₂(Lbar₁), O₂(L₁*) and common filtration top;
the source quotient identifications and final assembly remain separate.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels
open scoped commutatorElement

private theorem H2_normalizes_residual : H2 ≤ normalizer (Marked.residual : Set Symmetric) :=
  H2.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H2 (pResidual 2 H2))

theorem D0_le_residual : D0 ≤ Marked.residual := by
  have hc (s : Symmetric) (hs : s ∈ H2) : ⁅s, Marked.pairCycle⁆ ∈ Marked.residual := by
    exact Marked.residual.mul_mem
      ((mem_normalizer_iff.mp (H2_normalizes_residual hs) _).mp Marked.pairCycle_mem_residual)
      (Marked.residual.inv_mem Marked.pairCycle_mem_residual)
  have hab : swap01 * swap23 ∈ Marked.residual := by
    rw [show swap01 * swap23 = ⁅swap01, Marked.pairCycle⁆ by decide]
    exact hc swap01 (by decide)
  have hbc : swap23 * swap45 ∈ Marked.residual := by
    rw [show swap23 * swap45 = ⁅swap23, Marked.pairCycle⁆ by decide]
    exact hc swap23 (by decide)
  intro g hg
  rcases D0_cases hg with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hab
  · have he : swap01 * swap45 = (swap01 * swap23) * (swap23 * swap45) := by decide
    rw [he]
    exact mul_mem hab hbc
  · exact hbc

theorem residual_core_eq_D0 : Marked.residual.pCoreIn 2 = D0 := by
  apply le_antisymm
  · have hn : H2 ≤ normalizer (Marked.residual.pCoreIn 2 : Set Symmetric) :=
      H2_normalizes_residual.trans
        (normalizer_le_normalizer_characteristic_image Marked.residual (pCore 2 Marked.residual))
    have hd : Marked.residual.pCoreIn 2 ≤ D := by
      rw [← H2_core_eq_D]
      exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Marked.residual)
        ((pCoreIn_le 2 Marked.residual).trans Marked.residual_le_H2) hn
    exact le_inf hd ((pCoreIn_le 2 Marked.residual).trans Marked.residual_le_alternating)
  · exact le_pCoreIn_of_normalizes (D_isPGroup.to_le inf_le_left) D0_le_residual
      (Marked.residual_le_H2.trans H2_normalizes_D0)

theorem outer_parabolic_core :
    (H2.pCoreIn 2).map Marked.outer.toMonoidHom = H1.pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 H2 _ Marked.outer.injective, Marked.outer_H2]

theorem outer_residual_core :
    (Marked.residual.pCoreIn 2).map Marked.outer.toMonoidHom = K.pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 Marked.residual _ Marked.outer.injective, Marked.outer_residual]

theorem H1_core_eq_outer_D : H1.pCoreIn 2 = D.map Marked.outer.toMonoidHom := by
  rw [← outer_parabolic_core, H2_core_eq_D]

theorem K_core_eq_outer_D0 : K.pCoreIn 2 = D0.map Marked.outer.toMonoidHom := by
  rw [← outer_residual_core, residual_core_eq_D0]

private theorem fixedIndex_map (A R : Subgroup Symmetric) :
    (centralizer (A.map Marked.outer.toMonoidHom : Set Symmetric)).relIndex
      (R.map Marked.outer.toMonoidHom) = (centralizer (A : Set Symmetric)).relIndex R := by
  rw [← relIndex_comap]
  congr 1
  ext g
  constructor
  · intro hg a ha
    apply Marked.outer.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hg (Marked.outer a) (mem_map_of_mem _ ha)
  · intro hg a ha
    obtain ⟨b, hb, rfl⟩ := ha
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg Marked.outer (hg b hb)

theorem cubicActor_normalizes_parabolic_core :
    cubicActor ≤ normalizer (H2.pCoreIn 2 : Set Symmetric) := by
  rw [H2_core_eq_D]
  exact cubicActor_le_H2.trans H2_normalizes_D

theorem cubicActor_normalizes_residual_core :
    cubicActor ≤ normalizer (Marked.residual.pCoreIn 2 : Set Symmetric) := by
  rw [residual_core_eq_D0]
  exact cubicActor_le_H2.trans H2_normalizes_D0

theorem duadCubicActor_normalizes_parabolic_core :
    duadCubicActor ≤ normalizer (H1.pCoreIn 2 : Set Symmetric) := by
  rw [← outer_parabolic_core]
  exact (map_mono cubicActor_normalizes_parabolic_core).trans (le_normalizer_map _)

theorem duadCubicActor_normalizes_residual_core :
    duadCubicActor ≤ normalizer (K.pCoreIn 2 : Set Symmetric) := by
  rw [← outer_residual_core]
  exact (map_mono cubicActor_normalizes_residual_core).trans (le_normalizer_map _)

theorem cubicActor_parabolic_core_fixedIndex :
    (centralizer (cubicActor : Set Symmetric)).relIndex (H2.pCoreIn 2) = 4 := by
  rw [H2_core_eq_D]
  exact rotation_fixedIndex_D

theorem cubicActor_residual_core_fixedIndex :
    (centralizer (cubicActor : Set Symmetric)).relIndex (Marked.residual.pCoreIn 2) = 4 := by
  rw [residual_core_eq_D0]
  exact rotation_fixedIndex_D0

theorem duadCubicActor_parabolic_core_fixedIndex :
    (centralizer (duadCubicActor : Set Symmetric)).relIndex (H1.pCoreIn 2) = 4 := by
  rw [← outer_parabolic_core, duadCubicActor, fixedIndex_map]
  exact cubicActor_parabolic_core_fixedIndex

theorem duadCubicActor_residual_core_fixedIndex :
    (centralizer (duadCubicActor : Set Symmetric)).relIndex (K.pCoreIn 2) = 4 := by
  rw [← outer_residual_core, duadCubicActor, fixedIndex_map]
  exact cubicActor_residual_core_fixedIndex

theorem cubicActor_parabolic_core_length : conjugationCubicLength cubicActor (H2.pCoreIn 2) = 1 := by
  rw [conjugationCubicLength, cubicActor_parabolic_core_fixedIndex]
  decide

theorem cubicActor_residual_core_length :
    conjugationCubicLength cubicActor (Marked.residual.pCoreIn 2) = 1 := by
  rw [conjugationCubicLength, cubicActor_residual_core_fixedIndex]
  decide

theorem duadCubicActor_parabolic_core_length :
    conjugationCubicLength duadCubicActor (H1.pCoreIn 2) = 1 := by
  rw [conjugationCubicLength, duadCubicActor_parabolic_core_fixedIndex]
  decide

theorem duadCubicActor_residual_core_length :
    conjugationCubicLength duadCubicActor (K.pCoreIn 2) = 1 := by
  rw [conjugationCubicLength, duadCubicActor_residual_core_fixedIndex]
  decide

theorem residual_core_le_parabolic_core : Marked.residual.pCoreIn 2 ≤ H2.pCoreIn 2 := by
  rw [residual_core_eq_D0, H2_core_eq_D]
  exact inf_le_left

theorem K_core_le_parabolic_core : K.pCoreIn 2 ≤ H1.pCoreIn 2 := by
  rw [← outer_residual_core, ← outer_parabolic_core]
  exact map_mono residual_core_le_parabolic_core

theorem cubicActor_core_section_length :
    sectionCubicLength cubicActor (Marked.residual.pCoreIn 2) (H2.pCoreIn 2) = 0 := by
  rw [sectionCubicLength, cubicActor_parabolic_core_length, cubicActor_residual_core_length]

theorem duadCubicActor_core_section_length :
    sectionCubicLength duadCubicActor (K.pCoreIn 2) (H1.pCoreIn 2) = 0 := by
  rw [sectionCubicLength, duadCubicActor_parabolic_core_length, duadCubicActor_residual_core_length]

/-- The literal outer restriction on the two parabolic cores. -/
noncomputable def parabolicCoreEquiv : H2.pCoreIn 2 ≃* H1.pCoreIn 2 :=
  (Marked.outer.subgroupMap (H2.pCoreIn 2)).trans (MulEquiv.subgroupCongr outer_parabolic_core)

/-- The literal outer restriction on the two residual cores. -/
noncomputable def residualCoreEquiv : Marked.residual.pCoreIn 2 ≃* K.pCoreIn 2 :=
  (Marked.outer.subgroupMap (Marked.residual.pCoreIn 2)).trans
    (MulEquiv.subgroupCongr outer_residual_core)

@[simp] theorem parabolicCoreEquiv_coe (r : H2.pCoreIn 2) :
    (parabolicCoreEquiv r : Symmetric) = Marked.outer r := rfl

@[simp] theorem residualCoreEquiv_coe (r : Marked.residual.pCoreIn 2) :
    (residualCoreEquiv r : Symmetric) = Marked.outer r := rfl

theorem outer_core_inclusion (r : Marked.residual.pCoreIn 2) :
    parabolicCoreEquiv (inclusion residual_core_le_parabolic_core r) =
      inclusion K_core_le_parabolic_core (residualCoreEquiv r) := rfl

theorem parabolicCoreEquiv_equivariant (a : cubicActor) (r : H2.pCoreIn 2) :
    letI := conjMulDistribMulActionOfLeNormalizer cubicActor (H2.pCoreIn 2)
      cubicActor_normalizes_parabolic_core
    letI := conjMulDistribMulActionOfLeNormalizer duadCubicActor (H1.pCoreIn 2)
      duadCubicActor_normalizes_parabolic_core
    parabolicCoreEquiv (a • r) = cubicActorEquiv a • parabolicCoreEquiv r := by
  apply Subtype.ext
  change Marked.outer ((a : Symmetric) * (r : Symmetric) * (a : Symmetric)⁻¹) =
    Marked.outer a * Marked.outer r * (Marked.outer a)⁻¹
  simp only [map_mul, map_inv]

theorem residualCoreEquiv_equivariant (a : cubicActor) (r : Marked.residual.pCoreIn 2) :
    letI := conjMulDistribMulActionOfLeNormalizer cubicActor (Marked.residual.pCoreIn 2)
      cubicActor_normalizes_residual_core
    letI := conjMulDistribMulActionOfLeNormalizer duadCubicActor (K.pCoreIn 2)
      duadCubicActor_normalizes_residual_core
    residualCoreEquiv (a • r) = cubicActorEquiv a • residualCoreEquiv r := by
  apply Subtype.ext
  change Marked.outer ((a : Symmetric) * (r : Symmetric) * (a : Symmetric)⁻¹) =
    Marked.outer a * Marked.outer r * (Marked.outer a)⁻¹
  simp only [map_mul, map_inv]

/-- Normality here is inside the parabolic core, not in the symmetric group. -/
instance residual_core_normal :
    ((Marked.residual.pCoreIn 2).subgroupOf (H2.pCoreIn 2)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer residual_core_le_parabolic_core).mpr
  rw [residual_core_eq_D0]
  exact (pCoreIn_le 2 H2).trans H2_normalizes_D0

instance K_core_normal : ((K.pCoreIn 2).subgroupOf (H1.pCoreIn 2)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer K_core_le_parabolic_core).mpr
  rw [← outer_parabolic_core, ← outer_residual_core]
  exact (map_mono (le_normalizer_of_normal_subgroupOf residual_core_le_parabolic_core)).trans
    (le_normalizer_map _)

theorem cubicActor_core_commutator :
    ⁅cubicActor, H2.pCoreIn 2⁆ ≤ Marked.residual.pCoreIn 2 := by
  rw [H2_core_eq_D, residual_core_eq_D0]
  exact rotation_commutator_le_D0

theorem duadCubicActor_core_commutator :
    ⁅duadCubicActor, H1.pCoreIn 2⁆ ≤ K.pCoreIn 2 := by
  rw [← outer_parabolic_core, ← outer_residual_core, duadCubicActor, ← map_commutator]
  exact map_mono cubicActor_core_commutator

private theorem quotient_trivial_of_commutator (A R N : Subgroup Symmetric)
    (hAR : A ≤ normalizer (R : Set Symmetric))
    (hAN : A ≤ normalizer (N : Set Symmetric)) [(N.subgroupOf R).Normal]
    (hc : ⁅A, R⁆ ≤ N) :
    letI := quotientConjugationAction A R N hAR hAN
    ∀ (a : A) (q : R ⧸ N.subgroupOf R), a • q = q := by
  let := conjMulDistribMulActionOfLeNormalizer A R hAR
  let := quotientConjugationAction A R N hAR hAN
  intro a q
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) q
  change (↑(a • r) : R ⧸ N.subgroupOf R) = ↑r
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (a : Symmetric) * (r : Symmetric) * (a : Symmetric)⁻¹ / (r : Symmetric) ∈ N
  exact hc (commutator_mem_commutator a.property r.property)

/-- Adding the parabolic core to the source residual core adds an actor-trivial quotient. -/
theorem cubicActor_core_quotient_trivial :
    letI := quotientConjugationAction cubicActor (H2.pCoreIn 2) (Marked.residual.pCoreIn 2)
      cubicActor_normalizes_parabolic_core cubicActor_normalizes_residual_core
    ∀ (a : cubicActor) (q : (H2.pCoreIn 2) ⧸ (Marked.residual.pCoreIn 2).subgroupOf (H2.pCoreIn 2)),
      a • q = q :=
  quotient_trivial_of_commutator _ _ _ _ _ cubicActor_core_commutator

theorem duadCubicActor_core_quotient_trivial :
    letI := quotientConjugationAction duadCubicActor (H1.pCoreIn 2) (K.pCoreIn 2)
      duadCubicActor_normalizes_parabolic_core duadCubicActor_normalizes_residual_core
    ∀ (a : duadCubicActor) (q : (H1.pCoreIn 2) ⧸ (K.pCoreIn 2).subgroupOf (H1.pCoreIn 2)),
      a • q = q :=
  quotient_trivial_of_commutator _ _ _ _ _ duadCubicActor_core_commutator

/-- The zero difference is also the cubic length of the actual relative quotient. -/
theorem cubicActor_core_quotient_length :
    letI := quotientConjugationAction cubicActor (H2.pCoreIn 2) (Marked.residual.pCoreIn 2)
      cubicActor_normalizes_parabolic_core cubicActor_normalizes_residual_core
    FixedPoints.cubicLength cubicActor
      ((H2.pCoreIn 2) ⧸ (Marked.residual.pCoreIn 2).subgroupOf (H2.pCoreIn 2)) = 0 := by
  rw [← sectionCubicLength_eq_quotient_of_twoGroup _ _ _ cubicActor_isPGroup
    (isPGroup_pCoreIn 2 H2) residual_core_le_parabolic_core]
  exact cubicActor_core_section_length

theorem duadCubicActor_core_quotient_length :
    letI := quotientConjugationAction duadCubicActor (H1.pCoreIn 2) (K.pCoreIn 2)
      duadCubicActor_normalizes_parabolic_core duadCubicActor_normalizes_residual_core
    FixedPoints.cubicLength duadCubicActor
      ((H1.pCoreIn 2) ⧸ (K.pCoreIn 2).subgroupOf (H1.pCoreIn 2)) = 0 := by
  rw [← sectionCubicLength_eq_quotient_of_twoGroup _ _ _ duadCubicActor_isPGroup
    (isPGroup_pCoreIn 2 H1) K_core_le_parabolic_core]
  exact duadCubicActor_core_section_length

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels
