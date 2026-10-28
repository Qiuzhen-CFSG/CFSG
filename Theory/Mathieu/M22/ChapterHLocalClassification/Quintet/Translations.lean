module

public import Theory.Mathieu.M22.ChapterHLocalClassification.SextetRestriction
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.Spaces
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions

/-!
# The native inner and outer quintet translation modules

Restrict the source sextet E64 to the pointwise and setwise stabilizers of
{0,9}. Its action on the tetrad {0,2,9,14} is transitive. Commutativity makes
the stabilizer of 0 fix 9 as well, so orbit--stabilizer gives the inner order
16. A certified native translation exchanges 0 and 9; the inner intersection
therefore has index two and the outer translation group has order 32.

Both groups carry their literal conjugation actions under the outer quintet
stabilizer Q. Their normality is relative to Q. They are elementary abelian
of dimensions four and five. Identification with the intrinsic quintet cores,
the S5 quotient and the natural/indecomposable module assertions remain
separate obligations; none is assumed in these constructions.

Source: Aschbacher--Smith H.14.3(1--2), printed p.397, with the setup on p.396.
The generator table and its source marking reuse the native certificates in
`M24.LocalGeometry.EvenCandidates`, `SextetCore.Candidate` and
`M22.LocalStructure`. The hexacode comparison and its ATLAS attribution are
in the imported `SextetRestriction`; no new port is used here.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode MathieuCode.M22Quintet
open scoped Pointwise IsMulCommutative
namespace Sporadic.Mathieu.M22ChapterH.Quintet
open Sextet

abbrev outerTranslationGroup := outerTranslations
abbrev innerTranslationGroup := outerTranslations ⊓ L

private theorem elementary_of_injective {G H : Type*} [Group G] [Group H]
    [IsElementaryAbelian 2 H] (f : G →* H) (hf : Function.Injective f) :
    IsElementaryAbelian 2 G where
  is_comm := ⟨fun a b => hf (by simp only [map_mul]; exact mul_comm _ _)⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => hf (by
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 H) (f a))

instance outerTranslationGroup_elementary : IsElementaryAbelian 2 outerTranslationGroup := by
  let := sourceCore_elementary
  let f : outerTranslationGroup →* sourceCore :=
    (m22PairStabilizer.subtype.comp outerTranslationGroup.subtype).codRestrict _
      (fun g => g.property)
  apply elementary_of_injective f
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : sourceCore => x.val) h

instance innerTranslationGroup_elementary : IsElementaryAbelian 2 innerTranslationGroup :=
  elementary_of_injective (Subgroup.inclusion inf_le_left)
    (Subgroup.inclusion_injective inf_le_left)

theorem innerTranslations_map :
    innerTranslations.map m22ToPairStabilizer = innerTranslationGroup :=
  innerTranslations_map_pair

private theorem source_normalizer : sextetStabilizer m22SourceSextet ≤
    Subgroup.normalizer (sourceCore : Set M24) := by
  have h := (pCore 2 (sextetStabilizer m22SourceSextet)).le_normalizer_map
    (sextetStabilizer m22SourceSextet).subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

theorem outerTranslationGroup_normalizer : Q ≤
    Subgroup.normalizer (outerTranslationGroup : Set m22PairStabilizer) :=
  (Subgroup.comap_mono source_normalizer).trans (Subgroup.le_normalizer_comap _)

theorem inner_normal : L.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hx0 := (m22ToPairStabilizer_mem_range_iff_fixed_zero x).mp hx
  have hx9 : x.val • (9 : Fin 24) = 9 := by
    obtain ⟨y, rfl⟩ := hx
    exact m22Embedding_fixed_nine y
  apply (m22ToPairStabilizer_mem_range_iff_fixed_zero _).mpr
  have hm : g.val⁻¹ • (0 : Fin 24) ∈ m22Pair :=
    (MulAction.mem_stabilizer_finset'.mp g⁻¹.property) (by decide)
  have hp : g.val⁻¹ • (0 : Fin 24) = 0 ∨ g.val⁻¹ • (0 : Fin 24) = 9 := by
    simpa [m22Pair] using hm
  change g.val • (x.val • (g.val⁻¹ • (0 : Fin 24))) = 0
  have he : x.val • (g.val⁻¹ • (0 : Fin 24)) = g.val⁻¹ • (0 : Fin 24) := by
    rcases hp with h | h <;> rw [h]
    · exact hx0
    · exact hx9
  rw [he, smul_inv_smul]

theorem innerTranslationGroup_normalizer : Q ≤
    Subgroup.normalizer (innerTranslationGroup : Set m22PairStabilizer) := by
  let : L.Normal := inner_normal
  exact (le_inf outerTranslationGroup_normalizer
    (show Q ≤ Subgroup.normalizer (L : Set m22PairStabilizer) by
      rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

def outerTranslationConjugation :
    Representation (ZMod 2) Q (Additive outerTranslationGroup) :=
  Representation.BinaryInternalFixedSpaceCodimension.representation _ _
    outerTranslationGroup_normalizer

def innerTranslationConjugation :
    Representation (ZMod 2) Q (Additive innerTranslationGroup) :=
  Representation.BinaryInternalFixedSpaceCodimension.representation _ _
    innerTranslationGroup_normalizer

@[simp] theorem outerTranslationConjugation_apply (g : Q) (v : Additive outerTranslationGroup) :
    (outerTranslationConjugation g v).toMul.val = g.val * v.toMul.val * g.val⁻¹ := rfl

@[simp] theorem innerTranslationConjugation_apply (g : Q) (v : Additive innerTranslationGroup) :
    (innerTranslationConjugation g v).toMul.val = g.val * v.toMul.val * g.val⁻¹ := rfl

def sourceGenerator (i : Fin 6) : M24 :=
  MulAut.conj m22GeometryConjugator
    (MulAut.conj SextetCore.transport (EvenCandidates.generator 1 i))

set_option maxRecDepth 4096 in
theorem sourceGenerator_mem (i : Fin 6) : sourceGenerator i ∈ sourceCore := by
  rw [sourceCore_eq_conjugate]
  apply Subgroup.mem_map_of_mem
  rw [← SextetCore.standardCandidate_eq_core]
  exact Subgroup.mem_map_of_mem (MulAut.conj SextetCore.transport).toMonoidHom
    (EvenCandidates.generator_mem 1 i)

private theorem conjugate_point (c g : M24) (x : Fin 24) :
    (MulAut.conj c g).val x = c.val (g.val (c.val.symm x)) := rfl

set_option maxRecDepth 4096 in
theorem sourceGenerator_apply (i : Fin 6) (x : Fin 24) :
    (sourceGenerator i).val x = m22GeometryConjugator.val
      (SextetCore.transportPerm (EvenCandidates.generatorPoint 1 i
        (SextetCore.transportPerm.symm (m22GeometryConjugator.val.symm x)))) := by
  rw [sourceGenerator, conjugate_point, conjugate_point, EvenCandidates.generator_apply]
  rfl

set_option maxRecDepth 4096 in
private theorem sourceGenerator_three_pair :
    sourceGenerator 3 • m22Pair = m22Pair := by
  change m22Pair.image (sourceGenerator 3).val = m22Pair
  simp only [m22Pair, Finset.image_insert, Finset.image_singleton, sourceGenerator_apply]
  decide +kernel

def pairSwap : m22PairStabilizer := ⟨sourceGenerator 3, by exact sourceGenerator_three_pair⟩

theorem pairSwap_mem : pairSwap ∈ outerTranslationGroup := sourceGenerator_mem 3

set_option maxRecDepth 4096 in
@[simp] theorem pairSwap_zero : pairSwap.val • (0 : Fin 24) = 9 := by
  change (sourceGenerator 3).val 0 = 9
  rw [sourceGenerator_apply]
  decide +kernel

set_option maxRecDepth 4096 in
@[simp] theorem pairSwap_nine : pairSwap.val • (9 : Fin 24) = 0 := by
  change (sourceGenerator 3).val 9 = 0
  rw [sourceGenerator_apply]
  decide +kernel

theorem pairSwap_not_inner : pairSwap ∉ L := by
  rw [L, m22ToPairStabilizer_mem_range_iff_fixed_zero, pairSwap_zero]
  decide

/-- Every subgroup containing this translation has inner intersection of index two. -/
theorem innerIntersection_index (H : Subgroup m22PairStabilizer) (hH : pairSwap ∈ H) :
    (H ⊓ L).relIndex H = 2 := by
  apply Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨pairSwap, hH, fun h => pairSwap_not_inner h.2, ?_⟩
  intro b hb
  by_cases hi : b ∈ L
  · exact Or.inr ⟨hb, hi⟩
  left
  refine ⟨H.mul_mem hb hH, ?_⟩
  have hib : b⁻¹ ∉ m22ToPairStabilizer.range := by
    intro h
    exact hi (L.inv_mem h)
  have he := m22PairStabilizer_swaps_of_not_mem_range b⁻¹ hib
  apply (m22ToPairStabilizer_mem_range_iff_fixed_zero _).mpr
  change b.val • (pairSwap.val • (0 : Fin 24)) = 0
  rw [pairSwap_zero, ← he]
  exact smul_inv_smul b.val _

theorem innerTranslationGroup_index : innerTranslationGroup.relIndex outerTranslationGroup = 2 :=
  innerIntersection_index _ pairSwap_mem

theorem sourceCore_fixes_tetrad (g : M24) (hg : g ∈ sourceCore) (i : Fin 6) :
    g • m22SourceTetrad i = m22SourceTetrad i := by
  rw [sourceCore_eq_conjugate] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  rw [← SextetCore.standardCandidate_eq_core] at hx
  have hs := Subgroup.mem_iInf.mp (SextetCore.standardCandidate_le_partFixers hx) i
  change x • standardTetrad i = standardTetrad i at hs
  rw [m22SourceTetrad_eq_smul]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_smul, inv_smul_smul, hs]

set_option maxRecDepth 4096 in
private theorem generator_zero_table :
    (sourceGenerator 0).val 0 = 14 ∧ (sourceGenerator 1).val 0 = 2 := by
  simp only [sourceGenerator_apply]
  decide +kernel

set_option maxRecDepth 4096 in
/-- The source E64 acts transitively on its tetrad containing the deleted pair. -/
theorem sourceCore_orbit_zero : MulAction.orbit sourceCore (0 : Fin 24) =
    (m22SourceTetrad 0 : Set (Fin 24)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have h := sourceCore_fixes_tetrad g.val g.property 0
    exact (MulAction.mem_stabilizer_finset'.mp h) (by decide)
  · intro hx
    have hx' : x = 0 ∨ x = 2 ∨ x = 9 ∨ x = 14 := by
      simpa [m22SourceTetrad] using hx
    rcases hx' with rfl | rfl | rfl | rfl
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨⟨sourceGenerator 1, sourceGenerator_mem 1⟩, generator_zero_table.2⟩
    · refine ⟨⟨sourceGenerator 3, sourceGenerator_mem 3⟩, ?_⟩
      exact_mod_cast pairSwap_zero
    · exact ⟨⟨sourceGenerator 0, sourceGenerator_mem 0⟩, generator_zero_table.1⟩

/-- Orbit--stabilizer computes the order of the source translation point stabilizer. -/
theorem sourceCore_pointStabilizer_card :
    Nat.card (MulAction.stabilizer sourceCore (0 : Fin 24)) = 16 := by
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup sourceCore (0 : Fin 24))
  rw [Nat.card_prod, sourceCore_card, sourceCore_orbit_zero] at hc
  have ht : Nat.card {x : Fin 24 // x ∈ m22SourceTetrad 0} = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  change Nat.card {x : Fin 24 // x ∈ m22SourceTetrad 0} * _ = 64 at hc
  rw [ht] at hc
  omega

private theorem sourceCore_commute (g h : M24) (hg : g ∈ sourceCore)
    (hh : h ∈ sourceCore) : g * h = h * g := by
  let := sourceCore_elementary
  exact congrArg (fun x : sourceCore => x.val)
    (mul_comm (⟨g, hg⟩ : sourceCore) ⟨h, hh⟩)

set_option maxRecDepth 4096 in
private theorem sourceCore_fixed_nine (g : sourceCore)
    (hg : g.val • (0 : Fin 24) = 0) : g.val • (9 : Fin 24) = 9 := by
  have hc := sourceCore_commute g.val (sourceGenerator 3) g.property (sourceGenerator_mem 3)
  calc
    g.val • (9 : Fin 24) = g.val • (sourceGenerator 3 • (0 : Fin 24)) := by
      rw [show sourceGenerator 3 • (0 : Fin 24) = 9 from pairSwap_zero]
    _ = sourceGenerator 3 • (g.val • (0 : Fin 24)) := by
      simpa only [mul_smul] using congrArg (fun a : M24 => a • (0 : Fin 24)) hc
    _ = 9 := by rw [hg]; exact pairSwap_zero

/-- The native M22 restriction is the point stabilizer in the actual source E64. -/
def innerToSourcePointStabilizer :
    innerTranslations →* MulAction.stabilizer sourceCore (0 : Fin 24) where
  toFun g := ⟨⟨m22Embedding g.val, g.property⟩, m22Embedding_fixed_zero g.val⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one m22Embedding
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact map_mul m22Embedding a.val b.val

theorem innerToSourcePointStabilizer_bijective :
    Function.Bijective innerToSourcePointStabilizer := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply m22Embedding_injective
    exact congrArg (fun g : MulAction.stabilizer sourceCore (0 : Fin 24) => g.val.val) h
  · intro g
    have h0 : g.val.val • (0 : Fin 24) = 0 := g.property
    have hr : g.val.val ∈ m22Embedding.range := by
      rw [m22Embedding_range]
      exact ⟨h0, sourceCore_fixed_nine g.val h0⟩
    obtain ⟨a, ha⟩ := hr
    refine ⟨⟨a, ?_⟩, ?_⟩
    · change m22Embedding a ∈ sourceCore
      rw [ha]
      exact g.val.property
    · apply Subtype.ext
      exact Subtype.ext ha

def innerSourcePointStabilizerEquiv :
    innerTranslations ≃* MulAction.stabilizer sourceCore (0 : Fin 24) :=
  MulEquiv.ofBijective innerToSourcePointStabilizer innerToSourcePointStabilizer_bijective

theorem innerTranslations_card : Nat.card innerTranslations = 16 :=
  (Nat.card_congr innerSourcePointStabilizerEquiv.toEquiv).trans sourceCore_pointStabilizer_card

theorem innerTranslationGroup_card : Nat.card innerTranslationGroup = 16 := by
  rw [← innerTranslations_map]
  rw [Subgroup.card_map_of_injective]
  · exact innerTranslations_card
  · intro a b h
    exact m22Embedding_injective (congrArg Subtype.val h)

theorem outerTranslationGroup_card : Nat.card outerTranslationGroup = 32 := by
  have h := (innerTranslationGroup.subgroupOf outerTranslationGroup).card_mul_index
  have he : Nat.card (innerTranslationGroup.subgroupOf outerTranslationGroup) =
      Nat.card innerTranslationGroup :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [he, innerTranslationGroup_card] at h
  change 16 * innerTranslationGroup.relIndex outerTranslationGroup = _ at h
  rw [innerTranslationGroup_index] at h
  exact h.symm

def innerTranslationGroupEquiv : Sextet.innerTranslations ≃* innerTranslationGroup :=
  (Sextet.innerTranslations.equivMapOfInjective m22ToPairStabilizer
    (fun _ _ h => m22Embedding_injective (congrArg Subtype.val h))).trans
    (MulEquiv.subgroupCongr innerTranslations_map)

@[simp] theorem innerTranslationGroupEquiv_apply (g : Sextet.innerTranslations) :
    (innerTranslationGroupEquiv g).val = m22ToPairStabilizer g.val := rfl

theorem outerTranslationGroup_finrank :
    Module.finrank (ZMod 2) (Additive outerTranslationGroup) = 5 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive outerTranslationGroup)
  simpa only [Nat.card_zmod,
    Nat.card_congr (Additive.toMul : Additive outerTranslationGroup ≃ outerTranslationGroup),
    outerTranslationGroup_card] using h.symm

theorem innerTranslationGroup_finrank :
    Module.finrank (ZMod 2) (Additive innerTranslationGroup) = 4 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive innerTranslationGroup)
  simpa only [Nat.card_zmod,
    Nat.card_congr (Additive.toMul : Additive innerTranslationGroup ≃ innerTranslationGroup),
    innerTranslationGroup_card] using h.symm

end Sporadic.Mathieu.M22ChapterH.Quintet
