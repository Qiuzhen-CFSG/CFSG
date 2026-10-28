module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Actions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction.Descent
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction.CoreKernel

/-!
# Constructing the source local action for dimension doubling

From the earlier local identities and compatible marked isomorphisms, construct
an S₃-action on the literal U₂/V₂. First I₂ normalizes U₂. The point-core
commutator bound from 13.7.3(6) and the marked natural plane prove that O₂(I₂)
acts trivially, so actual conjugation descends along I₂/O₂(I₂) ≃ S₃.

The earlier local core bounds make the cubic commute with the canonical K₂
representation. A lift of the marked inverter lies in O₂(G₁), which centralizes
U_H/V₁ and hence fixes the whole three-space orbit modulo V₂. The marked
natural action on V/V₂ proves the seed polynomial and two-direction spanning.
No quotient action, fixedness, spanning, dimension, or decomposition is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6, printed p.948; 13.5.4(1),(2),(6), and 13.7.3(6).
`of_source_data` constructs the entire required action from the earlier local
conclusions and compatible markings authorized for this prerequisite. The
parent supplies those source conclusions and markings in final assembly.
The alternative `of_core_centrality` interface is retained as a conditional
helper; `of_source_data` proves the kernel directly and does not require G.2.2.
-/

public section

open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
variable {G : Type*} [Group G]

variable (H V V₁ V₂ V₃ I₂ L₂ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

/-- Descend actual conjugation and verify all four action properties once the
local core kernel is known. The source wrapper below proves that kernel. -/
theorem of_local_core_centrality [Finite G]
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hcore : ⁅Source.U2 H V V₂, I₂.pCoreIn 2⁆ ≤ V₂)
    (a : V₃) (ha : (a : G) ∉ V₂) :
    Nonempty (LocalDoublingAction H V V₂ V₃ d.flag3V a) := by
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
  refine ⟨{
    symmetric := σ
    seed_polynomial := hpoly
    seed_plane := hplane
    commutes := ?_
    fixes_orbit := ?_ }⟩
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

/-- The previously available route from the G₂-core centrality conclusion.
This conditional interface does not assert applicability of G.2.2. -/
theorem of_core_centrality [Finite G]
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hcentral : ⁅conjugateSpanBy V (normalizer (V₂ : Set G)),
      (normalizer (V₂ : Set G)).pCoreIn 2⁆ ≤ V₂)
    (a : V₃) (ha : (a : G) ∉ V₂) :
    Nonempty (LocalDoublingAction H V V₂ V₃ d.flag3V a) :=
  of_local_core_centrality H V V₁ V₂ V₃ I₂ L₂ d m
    (local_core_centrality H V V₂ I₂ _ d.normalClosure d.point_core_le_G2 hcentral) a ha

/-- Construct the genuine local action from the earlier source subgroup
identities and compatible model markings. The extra displayed commutator bound
is the inclusion in [V,Q_H] = V₃ from 13.7.3(6). The kernel on U₂/V₂, the cubic
commutation, seed polynomial, orbit fixedness and seed spanning are all proved.
No action or doubling conclusion is a premise. -/
theorem of_source_data [Finite G]
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃)
    (a : V₃) (ha : (a : G) ∉ V₂) :
    Nonempty (LocalDoublingAction H V V₂ V₃ d.flag3V a) :=
  of_local_core_centrality H V V₁ V₂ V₃ I₂ L₂ d m
    (U2_core_centrality H V V₁ V₂ V₃ I₂ L₂ d m hVQ a ha) a ha

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
