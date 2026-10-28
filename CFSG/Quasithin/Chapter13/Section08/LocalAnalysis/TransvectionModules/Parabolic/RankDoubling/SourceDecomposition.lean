module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling
/-!
# The actual cubic in the two-orbit decomposition

The source local action on U₂/V₂ is built with a specified lift r in L₂
of its cubic. The previously proved two-coordinate equivalence therefore
expresses U₂ as the join of B = ⟨V₃^{K₂}⟩ and its actual r-conjugate.
The denominator V₂ is retained when lifting the quotient equality.

This is the decomposition used in the proper U_L/U₀ branch of 13.8.33.
The consumer OriginalCoverPlane uses it to prove that the second local
image has order four; no splitting or dimension is assumed there.
Source: Aschbacher--Smith, 13.8.6(5) and proof of 13.8.33, printed pp.948,967.
-/

public section

open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
variable {G : Type*} [Group G]

variable (H V V₁ V₂ V₃ I₂ L₂ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

/-- Construct the local action with an actual cubic lift in L₂. -/
theorem local_action_with_cubic_lift [Finite G]
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hcore : ⁅Source.U2 H V V₂, I₂.pCoreIn 2⁆ ≤ V₂)
    (a : V₃) (ha : (a : G) ∉ V₂) :
    ∃ action : LocalDoublingAction H V V₂ V₃ d.flag3V a,
      ∃ r : I₂, (r : G) ∈ L₂ ∧
        action.symmetric InvertedCubicTensor.cubic =
          linearAction H V V₂ I₂ d.normalizes_U2 d.I2_le_G2 r := by
  let P := I₂ ⊔ Source.K2 H V₂
  have hPU : P ≤ normalizer (Source.U2 H V V₂ : Set G) :=
    sup_le d.normalizes_U2 (le_normalizer_conjugateSpanBy V (Source.K2 H V₂))
  have hK₂ : Source.K2 H V₂ ≤ normalizer (V₂ : Set G) :=
    (Source.K2_le_centralizer H V₂).trans (inf_le_right.trans (centralizer_le_normalizer _))
  have hP₂ : P ≤ normalizer (V₂ : Set G) := sup_le d.I2_le_G2 hK₂
  let ρ := linearAction H V V₂ P hPU hP₂
  let ρI : Representation F I₂ (Additive (Uhat H V V₂)) :=
    ρ.comp (inclusion (show I₂ ≤ P from le_sup_left))
  have hker : pCore 2 I₂ ≤ ρI.ker := by
    intro i hi
    exact linearAction_kills H V V₂ P (I₂.pCoreIn 2) hPU hP₂ hcore
      (show (i : G) ∈ I₂.pCoreIn 2 from ⟨i,hi,rfl⟩)
  let σ := descend H V V₂ I₂ ρI hker m.localEquiv
  obtain ⟨r, hrL, hr⟩ : ∃ r : I₂, (r : G) ∈ L₂ ∧
      m.localEquiv (QuotientGroup.mk' (pCore 2 I₂) r) = InvertedCubicTensor.cubic := by
    have hm := m.cubic_image.ge (mem_zpowers InvertedCubicTensor.cubic)
    exact hm
  obtain ⟨t, htQ, ht⟩ : ∃ t : I₂,
      (t : G) ∈ (normalizer (V₁ : Set G)).pCoreIn 2 ∧
      m.localEquiv (QuotientGroup.mk' (pCore 2 I₂) t) = InvertedCubicTensor.inverter := by
    have hm := m.inverter_image.ge (mem_zpowers InvertedCubicTensor.inverter)
    exact hm
  let rP : P := ⟨r, (show I₂ ≤ P from le_sup_left) r.property⟩
  let tP : P := ⟨t, (show I₂ ≤ P from le_sup_left) t.property⟩
  have hσr : σ InvertedCubicTensor.cubic = ρ rP := by
    rw [← hr]
    exact descend_mk H V V₂ I₂ ρI hker m.localEquiv r
  have hσt : σ InvertedCubicTensor.inverter = ρ tP := by
    rw [← ht]
    exact descend_mk H V V₂ I₂ ρI hker m.localEquiv t
  have hseed (b : V) : σ InvertedCubicTensor.cubic (seedVector H V V₂ b) =
      seedInclusion H V V₂ (m.planeEquiv.symm
        (BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic
          (m.planeEquiv (seedClass V V₂ b)))) := by
    have hm := m.equivariant ⟨r,hrL⟩ b
    have hr' : m.localEquiv (QuotientGroup.mk' (pCore 2 I₂)
        ⟨r, d.L2_le_I2 hrL⟩) = InvertedCubicTensor.cubic := hr
    rw [hr'] at hm
    rw [← hm, m.planeEquiv.symm_apply_apply, seedInclusion_mk, hσr]
    exact linearAction_mk H V V₂ P hPU hP₂ rP
      ⟨b, Source.seed_le_U2 H V V₂ b.property⟩
  obtain ⟨hpoly, hplane⟩ := marked_seed_facts H V V₂ m.planeEquiv
    (σ InvertedCubicTensor.cubic) hseed ⟨a,d.flag3V a.property⟩ ha
  let action : LocalDoublingAction H V V₂ V₃ d.flag3V a := by
    refine {
      symmetric := σ
      seed_polynomial := hpoly
      seed_plane := hplane
      commutes := ?_
      fixes_orbit := ?_ }
    · intro k x
      let kP : P := ⟨k, (show Source.K2 H V₂ ≤ P from le_sup_right) k.property⟩
      have hck : ⁅(rP : G), (kP : G)⁆ ∈ I₂.pCoreIn 2 := by
        have hc := core_bounds d.sylow H I₂ L₂ _ V₂ d.sylow_le_H d.sylow_le_G2
          d.point_core_le_G2 d.normalClosure d.residual d.centralizer
        rw [commutator_comm] at hc
        exact residual_core_le I₂ L₂ d.residual
          (hc (commutator_mem_commutator hrL k.property)).2
      have hc := linearAction_commute H V V₂ P (I₂.pCoreIn 2) hPU hP₂ hcore rP kP hck
      have hk : ρ kP = representation H V V₂ k :=
        linearAction_K2 H V V₂ P hPU hP₂ le_sup_right k
      rw [hσr, ← hk]
      exact congrArg (fun f => f x) hc.eq
    · intro k
      rw [hσt, seedVector, representation_mk]
      apply linearAction_fixed H V V₂ P hPU hP₂ tP
      have hw : (k : G) * (a : G) * (k : G)⁻¹ ∈ Source.UH H V₃ :=
        Subgroup.subset_closure ⟨k,Source.K2_le H V₂ k.property,a,a.property,rfl⟩
      have hc := d.point_core_commutator
      rw [commutator_comm] at hc
      exact d.flag12 (hc (commutator_mem_commutator htQ hw))

  refine ⟨action,r,hrL,?_⟩
  change σ InvertedCubicTensor.cubic = _
  rw [hσr]
  ext x
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective
    (V₂.subgroupOf (Source.U2 H V V₂)) x.toMul
  have hx : quotientMap H V V₂ (Additive.ofMul u) = x := congrArg Additive.ofMul hu
  rw [← hx,linearAction_mk,linearAction_mk]

/-- The earlier source data give a literal two-conjugate decomposition of U₂. -/
theorem source_two_conjugates [Finite G]
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (hindex : V₂.relIndex V₃ = 2) :
    ∃ r : I₂, (r : G) ∈ L₂ ∧
      Source.U2 H V V₂ = conjugateSpanBy V₃ (Source.K2 H V₂) ⊔
        (conjugateSpanBy V₃ (Source.K2 H V₂)).map (MulAut.conj (r : G)).toMonoidHom := by
  obtain ⟨a,ha,_⟩ := exists_seed_direction H V V₂ V₃ d.flag3V hindex
  obtain ⟨act,r,hrL,hr⟩ := local_action_with_cubic_lift H V V₁ V₂ V₃ I₂ L₂ d m
    (U2_core_centrality H V V₁ V₂ V₃ I₂ L₂ d m hVQ a ha) a ha
  let B := conjugateSpanBy V₃ (Source.K2 H V₂)
  let C := B ⊔ B.map (MulAut.conj (r : G)).toMonoidHom
  have hBU : B ≤ Source.U2 H V V₂ := conjugateSpanBy_mono d.flag3V le_rfl
  have hrU : (r : G) ∈ normalizer (Source.U2 H V V₂ : Set G) :=
    d.normalizes_U2 r.property
  have hCU : C ≤ Source.U2 H V V₂ := sup_le hBU (by
    rintro x ⟨b,hb,rfl⟩
    exact (mem_normalizer_iff.mp hrU b).mp (hBU hb))
  refine ⟨r,hrL,le_antisymm ?_ hCU⟩
  intro u hu
  obtain ⟨⟨x,y⟩,he⟩ := (sourcePairEquiv H V V₂ V₃ d.flag3V hindex a ha act).surjective
    (quotientMap H V V₂ (Additive.ofMul ⟨u,hu⟩))
  rw [sourcePairEquiv_apply,hr] at he
  have hx := x.property
  have hy := y.property
  simp only [W_eq_image_span] at hx hy
  obtain ⟨b,hb,hbx⟩ := hx
  obtain ⟨b',hb',hby⟩ := hy
  rw [← hbx,← hby] at he
  change quotientMap H V V₂ (Additive.ofMul b.toMul) +
    linearAction H V V₂ I₂ d.normalizes_U2 d.I2_le_G2 r
      (quotientMap H V V₂ (Additive.ofMul b'.toMul)) = _ at he
  rw [linearAction_mk] at he
  let br : Source.U2 H V V₂ := ⟨(r : G) * b'.toMul.val * (r : G)⁻¹,
    (mem_normalizer_iff.mp hrU _).mp b'.toMul.property⟩
  have he' : quotientMap H V V₂
      (Additive.ofMul (b.toMul * br) - Additive.ofMul ⟨u,hu⟩) = 0 := by
    rw [map_sub,sub_eq_zero]
    exact he
  have hv : (b.toMul.val * br.val) / u ∈ V₂ := (quotientMap_eq_zero H V V₂ _).mp he'
  have hbc : b.toMul.val * br.val ∈ C := C.mul_mem (mem_sup_left hb)
    (mem_sup_right (mem_map_of_mem _ hb'))
  have hvc : (b.toMul.val * br.val) / u ∈ C :=
    mem_sup_left (le_conjugateSpanBy V₃ (Source.K2 H V₂) (d.flag23 hv))
  have hc := C.mul_mem (C.inv_mem hvc) hbc
  simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hc

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
