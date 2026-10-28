module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction.Inputs
public import Theory.Representation.NormalInvariants
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# The local two-core acts trivially on the doubling quotient

The earlier identity [V,Q_H] = V₃ in 13.7.3(6) implies that I₂ normalizes V.
Its marked cubic acts naturally on V/V₂. A normal two-subgroup has a nonzero
fixed vector on this binary plane; the cubic orbit of that vector spans the
plane, and normality preserves its fixed space. Thus O₂(I₂) centralizes V/V₂.

Since I₂ is normal in G₂, K₂ normalizes O₂(I₂). The centrality bound therefore
propagates through the literal K₂-conjugate span U₂. This proves the kernel
needed for descent without assuming the G.2.2 conclusion or any dimensions
or decomposition of U₂/V₂. All normality statements are relative to the
indicated local overgroups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4(1), 13.7.3(6), and the doubling step of 13.8.6, printed p.948.
This is a direct modular fixed-vector proof of the needed centrality bound.
-/

public section

open Subgroup Module Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction

private theorem natural_core_le_ker {A : Type*} [Group A] [Finite A]
    (ρ : Representation F A NaturalPlane) (r : A)
    (hr : ∀ x, ρ r x = BinaryPermutation.coreRepresentation (Fin 3)
      InvertedCubicTensor.cubic x)
    (v : NaturalPlane) (hv : v ≠ 0) : pCore 2 A ≤ ρ.ker := by
  let : Nontrivial NaturalPlane := ⟨⟨v, 0, hv⟩⟩
  have hp : IsPGroup (ringChar F) (pCore 2 A) := by
    simpa only [F, ZMod.ringChar_zmod_n] using (pCore_isPGroup (p := 2) (G := A))
  obtain ⟨x, hx, hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (F := F) (by simp only [F, ZMod.ringChar_zmod_n, OfNat.ofNat_ne_zero, not_false_eq_true])
    hp (ρ.comp (pCore 2 A).subtype)
  let S := Representation.fixedSubrepresentationOfNormal ρ (pCore 2 A)
  have hxS : x ∈ S := hfix
  have hrx : BinaryPermutation.coreRepresentation (Fin 3)
      InvertedCubicTensor.cubic x ∈ S := by
    rw [← hr]
    exact S.apply_mem_toSubmodule r hxS
  have hspan : Submodule.span F {x, BinaryPermutation.coreRepresentation (Fin 3)
      InvertedCubicTensor.cubic x} ≤ S.toSubmodule :=
    Submodule.span_le.mpr (Set.insert_subset hxS (Set.singleton_subset_iff.mpr hrx))
  intro i hi
  apply MonoidHom.mem_ker.mpr
  apply LinearMap.ext
  intro y
  have hy : y ∈ S := hspan (natural_pair_spans x hx y)
  exact hy ⟨i,hi⟩

variable {G : Type*} [Group G] [Finite G]
variable (H V V₁ V₂ V₃ I₂ L₂ : Subgroup G)
  [IsElementaryAbelian 2 V]

namespace LocalData
variable {H V V₁ V₂ V₃ I₂ L₂}

omit [IsElementaryAbelian 2 V] in
/-- The source point-core commutator bound makes the full I₂ normalize V. -/
theorem normalizes_V (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) : I₂ ≤ normalizer (V : Set G) := by
  rw [d.product]
  apply sup_le _ d.L2_normalizes_V
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono le_rfl
    (point_core_le_Hcore d.sylow H V₁ d.sylow_le_H d.H_le_G1)).trans hVQ).trans d.flag3V

end LocalData

private noncomputable def seedConjugation
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂) (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) :
    I₂ →* MulAut (SeedQuotient V V₂) :=
  (exists_quotient_conjugation_action I₂ V V₂ (d.normalizes_V hVQ)
    d.I2_le_G2 inferInstance).choose

private theorem seedConjugation_mk
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂) (hVQ : ⁅V, Source.QH H⁆ ≤ V₃)
    (i : I₂) (b : V) :
    seedConjugation H V V₁ V₂ V₃ I₂ L₂ d hVQ i
      (QuotientGroup.mk' (V₂.subgroupOf V) b) =
    QuotientGroup.mk' (V₂.subgroupOf V)
      ⟨(i : G) * (b : G) * (i : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalizes_V hVQ i.property) b).mp b.property⟩ :=
  (exists_quotient_conjugation_action I₂ V V₂ (d.normalizes_V hVQ)
    d.I2_le_G2 inferInstance).choose_spec i b

private noncomputable def seedAction
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂) (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) :
    Representation F I₂ (Additive (SeedQuotient V V₂)) where
  toFun i := (seedConjugation H V V₁ V₂ V₃ I₂ L₂ d hVQ i).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext x
    change Additive.ofMul (seedConjugation H V V₁ V₂ V₃ I₂ L₂ d hVQ 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' p q := by
    ext x
    change Additive.ofMul (seedConjugation H V V₁ V₂ V₃ I₂ L₂ d hVQ (p * q) x.toMul) = _
    rw [map_mul]
    rfl

private theorem seedAction_mk
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂) (hVQ : ⁅V, Source.QH H⁆ ≤ V₃)
    (i : I₂) (b : V) :
    seedAction H V V₁ V₂ V₃ I₂ L₂ d hVQ i (seedClass V V₂ b) =
    seedClass V V₂ ⟨(i : G) * (b : G) * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalizes_V hVQ i.property) b).mp b.property⟩ := by
  simp only [seedClass_eq_mk]
  exact congrArg Additive.ofMul (seedConjugation_mk H V V₁ V₂ V₃ I₂ L₂ d hVQ i b)

/-- Derive the core kernel on the literal seed quotient from its marked cubic action. -/
theorem seed_core_centrality
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃)
    (a : V₃) (ha : (a : G) ∉ V₂) : ⁅V, I₂.pCoreIn 2⁆ ≤ V₂ := by
  let ρ := seedAction H V V₁ V₂ V₃ I₂ L₂ d hVQ
  let τ : Representation F I₂ NaturalPlane :=
    m.planeEquiv.conjRingEquiv.toMonoidHom.comp ρ
  obtain ⟨r, hrL, hr⟩ : ∃ r : I₂, (r : G) ∈ L₂ ∧
      m.localEquiv (QuotientGroup.mk' (pCore 2 I₂) r) = InvertedCubicTensor.cubic :=
    m.cubic_image.ge (mem_zpowers InvertedCubicTensor.cubic)
  have hrτ (x : NaturalPlane) : τ r x =
      BinaryPermutation.coreRepresentation (Fin 3) InvertedCubicTensor.cubic x := by
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (V₂.subgroupOf V) (m.planeEquiv.symm x).toMul
    have hb' : seedClass V V₂ b = m.planeEquiv.symm x := by
      rw [seedClass_eq_mk]
      exact congrArg Additive.ofMul hb
    change m.planeEquiv (ρ r (m.planeEquiv.symm x)) = _
    rw [← hb', seedAction_mk]
    have he := m.equivariant ⟨r,hrL⟩ b
    have hr' : m.localEquiv (QuotientGroup.mk' (pCore 2 I₂)
        ⟨r, d.L2_le_I2 hrL⟩) = InvertedCubicTensor.cubic := hr
    rw [hr', hb', m.planeEquiv.apply_symm_apply] at he
    exact he
  have hker := natural_core_le_ker τ r hrτ
    (m.planeEquiv (seedClass V V₂ ⟨a,d.flag3V a.property⟩))
    (marked_seed_ne_zero V V₂ m.planeEquiv ⟨a,d.flag3V a.property⟩ ha)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro i hi b hb
  obtain ⟨i, hi, rfl⟩ := hi
  have he : τ i (m.planeEquiv (seedClass V V₂ ⟨b,hb⟩)) =
      m.planeEquiv (seedClass V V₂ ⟨b,hb⟩) := by
    rw [MonoidHom.mem_ker.mp (hker hi)]
    rfl
  change m.planeEquiv (ρ i (m.planeEquiv.symm
    (m.planeEquiv (seedClass V V₂ ⟨b,hb⟩)))) = _ at he
  rw [m.planeEquiv.symm_apply_apply] at he
  have he' := m.planeEquiv.injective he
  rw [seedAction_mk] at he'
  simp only [seedClass_eq_mk] at he'
  have hmem := QuotientGroup.eq_iff_div_mem.mp he'
  change (i : G) * b * (i : G)⁻¹ / b ∈ V₂ at hmem
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hmem

variable [IsMulCommutative (Source.VH H V)]

/-- Extend the proved seed kernel through the actual K₂-conjugate generation. -/
theorem U2_core_centrality
    (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃)
    (a : V₃) (ha : (a : G) ∉ V₂) : ⁅Source.U2 H V V₂, I₂.pCoreIn 2⁆ ≤ V₂ := by
  have hV₂U : V₂ ≤ Source.U2 H V V₂ :=
    (d.flag23.trans d.flag3V).trans (Source.seed_le_U2 H V V₂)
  have hUV₂ : Source.U2 H V V₂ ≤ normalizer (V₂ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hV₂U).mp inferInstance
  have hKG₂ : Source.K2 H V₂ ≤ normalizer (V₂ : Set G) :=
    (Source.K2_le_centralizer H V₂).trans (inf_le_right.trans (centralizer_le_normalizer _))
  have hG₂I : normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) := by
    rw [d.normalClosure]
    exact le_normalizer_conjugateSpanBy _ _
  have hKQ : Source.K2 H V₂ ≤ normalizer (I₂.pCoreIn 2 : Set G) :=
    hKG₂.trans (hG₂I.trans (normalizer_le_normalizer_characteristic_image I₂ (pCore 2 I₂)))
  have hU : Source.U2 H V V₂ ≤ commutatorPreimage (Source.U2 H V V₂) (I₂.pCoreIn 2) V₂ :=
    conjugateSpanBy_le
      (le_commutatorPreimage (Source.seed_le_U2 H V V₂)
        (seed_core_centrality H V V₁ V₂ V₃ I₂ L₂ d m hVQ a ha))
      (commutatorPreimage_normalized _ _ _ _ hUV₂
        (le_normalizer_conjugateSpanBy V (Source.K2 H V₂)) hKQ hKG₂)
  exact (commutator_mono hU le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hUV₂)

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
