module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.RelativeCore
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Parity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.Orbit
public import Theory.GroupTheory.NormalizingInvolutionCard
import Mathlib.Tactic.FinCases

/-!
# The fixed Sylow subgroups in the Hall--Janko parabolics

The seven seed generators centralize the chosen involution. Its certified
315 conjugates give the centralizer index. Thus the independent first-local
order 1920 identifies the seed subgroup of order 128 as Sylow in the actual
ATLAS carrier. No comparison with another model of J₂ is used.

The fixed outer word is an odd involution normalizing the seed subgroup;
seven checked conjugation witnesses identify its action. Adjoining it doubles
the subgroup order to 256, just as adjoining the published normalizing
involution doubles the ambient order. This proves the outer Sylow assertion.

Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263; ATLAS
J2G1-p100B0. The fixed words and original data are retained beside Seed.lean.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
open Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 100000 in
private theorem sGenerator_commutes_check : ∀ i,
    sGenTable i * FirstFusion.tPerm = FirstFusion.tPerm * sGenTable i := by
  apply allFin
  decide +kernel

/-- The whole fixed two-subgroup lies in the first local centralizer. -/
theorem s_le_l₁ : s ≤ l₁ := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply inclusion_injective
  rw [map_mul, map_mul, sGenerator_inclusion]
  change _ * inclusion FirstFusion.t = inclusion FirstFusion.t * _
  rw [FirstFusion.inclusion_t]
  exact sGenerator_commutes_check i

/-- The checked conjugacy orbit belongs to the literal first Seed factor. -/
theorem l₁_index : l₁.index = 315 := FirstFusion.centralizer_index

/-- Only the independent first-local cardinality is needed for the ambient order. -/
theorem card_carrier (h₁ : Nat.card l₁ = 1920) : Nat.card Carrier = 604800 := by
  have h := l₁.card_mul_index
  rw [h₁, l₁_index] at h
  exact h.symm

/-- The fixed subgroup has odd index in the carrier. -/
theorem s_index (h₁ : Nat.card l₁ = 1920) : s.index = 4725 := by
  have h := s.card_mul_index
  rw [card_s, card_carrier h₁] at h
  omega

/-- The Sylow subgroup uses the unchanged seven Seed words. -/
def sylow (h₁ : Nat.card l₁ = 1920) : Sylow 2 Carrier :=
  (IsPGroup.of_card (n := 7) card_s).toSylow (by rw [s_index h₁]; decide)

@[simp] theorem sylow_coe (h₁ : Nat.card l₁ = 1920) : (sylow h₁ : Subgroup Carrier) = s := rfl

@[simp] theorem card_sylow (h₁ : Nat.card l₁ = 1920) : Nat.card (sylow h₁) = 128 := card_s

/-- Checked table of the fixed outer Seed word. -/
def outerValues : Fin 100 → Fin 100 :=
  ![0, 1, 64, 74, 26, 84, 31, 7, 43, 47, 16, 80, 67, 73, 40, 95, 10, 58, 38, 76,
    83, 68, 42, 69, 24, 57, 4, 45, 29, 28, 90, 6, 41, 33, 86, 85, 52, 49, 18, 56,
    14, 32, 22, 8, 53, 27, 60, 9, 78, 37, 65, 51, 36, 44, 79, 55, 39, 25, 17, 87,
    46, 71, 75, 63, 2, 50, 72, 12, 21, 23, 94, 61, 66, 13, 3, 62, 19, 88, 48, 54,
    11, 81, 82, 20, 5, 35, 34, 59, 77, 89, 30, 92, 91, 93, 70, 15, 96, 97, 99, 98]

set_option maxRecDepth 100000 in
theorem outerValues_involutive : Function.Involutive outerValues := by
  change ∀ x, outerValues (outerValues x) = x
  decide +kernel

/-- The certificate table is compared with the actual word below. -/
def outerTable : Equiv.Perm (Fin 100) :=
  tablePerm outerValues outerValues outerValues_involutive outerValues_involutive

set_option maxRecDepth 2000 in
private theorem extension_word_inclusion (w : List (Fin 4)) :
    extension.subtype (evalWord ![intoExtension a, intoExtension b, intoExtension b⁻¹,
      extensionInvolution] w) = evalWord ![tableA, tableB, tableB⁻¹, involution] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [evalWord, map_mul, ih, evalWord]
    congr 1
    fin_cases i
    · exact generatorA_eq_table
    · exact generatorB_eq_table
    · change generatorB⁻¹ = tableB⁻¹
      rw [generatorB_eq_table]
    · rfl

set_option maxRecDepth 100000 in
private theorem outer_word_check :
    evalWord ![tableA, tableB, tableB⁻¹, involution] outerWord = outerTable := by
  decide +kernel

/-- The table represents exactly Seed.outerElement. -/
theorem outerElement_inclusion : extension.subtype outerElement = outerTable :=
  (extension_word_inclusion outerWord).trans outer_word_check

/-- The fixed outer word is an involution in the actual extension. -/
theorem outerElement_sq : outerElement ^ 2 = 1 := by
  apply extension.subtype_injective
  rw [map_pow, map_one, outerElement_inclusion]
  decide +kernel

set_option maxRecDepth 100000 in
theorem outerElement_sign : Equiv.Perm.sign (extension.subtype outerElement) = -1 := by
  rw [outerElement_inclusion]
  decide +kernel

/-- Injectivity of the actual carrier inclusion. -/
theorem intoExtension_injective : Function.Injective intoExtension :=
  Subgroup.inclusion_injective _

/-- The fixed outer word lies outside even the whole inner carrier. -/
theorem outerElement_not_mem_range : outerElement ∉ intoExtension.range := by
  rintro ⟨x, hx⟩
  have he : Equiv.Perm.sign (extension.subtype (intoExtension x)) = 1 :=
    generated_le_sign_ker x.property
  rw [hx, outerElement_sign] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

/-- Indices in the checked 128-element seed enumeration. -/
def outerConjIndex : Fin 7 → Fin 128 := ![57, 30, 1, 117, 24, 64, 6]

set_option maxRecDepth 100000 in
private theorem outer_conj_check : ∀ i,
    outerTable * sGenTable i * outerTable⁻¹ = sTable (outerConjIndex i) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 2000 in
/-- Exact conjugation witnesses for all seven unchanged Sylow generators. -/
theorem outerElement_conj_sGenerator (i : Fin 7) :
    outerElement * intoExtension (sGenerator i) * outerElement⁻¹ =
      intoExtension (sElement (outerConjIndex i)) := by
  apply extension.subtype_injective
  rw [map_mul, map_mul, map_inv, outerElement_inclusion]
  change outerTable * inclusion (sGenerator i) * outerTable⁻¹ = inclusion (sElement _)
  rw [sGenerator_inclusion, sElement_inclusion]
  exact outer_conj_check i

set_option maxRecDepth 2000 in
/-- The fixed outer involution normalizes the fixed inner two-subgroup. -/
theorem outerElement_normalizes_s :
    outerElement ∈ Subgroup.normalizer (s.map intoExtension : Set Extension) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hle : (s.map intoExtension).map (MulAut.conj outerElement).toMonoidHom ≤
      s.map intoExtension := by
    rw [Subgroup.map_map, Subgroup.map_le_iff_le_comap]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change outerElement * intoExtension (sGenerator i) * outerElement⁻¹ ∈ s.map intoExtension
    rw [outerElement_conj_sGenerator]
    exact Subgroup.mem_map_of_mem _ (sElement_mem _)
  apply le_antisymm hle
  intro x hx
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj outerElement) x,
    hle (Subgroup.mem_map_of_mem _ hx), ?_⟩
  change outerElement * (outerElement * x * outerElement⁻¹) * outerElement⁻¹ = x
  have ht : outerElement * outerElement = 1 := by simpa only [pow_two] using outerElement_sq
  have hi : outerElement⁻¹ = outerElement := inv_eq_of_mul_eq_one_left ht
  rw [hi]
  simp only [← mul_assoc, one_mul, mul_assoc x, ht, mul_one]

/-- The outer Sylow candidate has order 256, with all word checks discharged. -/
theorem card_outerS : Nat.card outerS = 256 := by
  rw [outerS, Subgroup.card_sup_zpowers_of_normalizing_involution _ _ outerElement_sq
    (fun h => outerElement_not_mem_range ((s.map_le_range intoExtension) h))
    outerElement_normalizes_s,
    Subgroup.card_map_of_injective intoExtension_injective, card_s]

/-- The explicit permutation extension doubles the original carrier order. -/
theorem card_extension (h₁ : Nat.card l₁ = 1920) : Nat.card Extension = 1209600 := by
  have h : Nat.card extension = 2 * Nat.card generated :=
    Subgroup.card_sup_zpowers_of_normalizing_involution _ _
      (by simpa only [pow_two] using involution_mul_self)
      involution_not_mem_generated involution_mem_normalizer
  change Nat.card Extension = _
  change Nat.card Extension = 2 * Nat.card Carrier at h
  rw [card_carrier h₁] at h
  exact h

/-- The outer subgroup also has odd index 4725. -/
theorem outerS_index (h₁ : Nat.card l₁ = 1920) : outerS.index = 4725 := by
  have h := outerS.card_mul_index
  rw [card_outerS, card_extension h₁] at h
  omega

/-- The concrete outer Sylow uses exactly Seed.outerS. -/
def outerSylow (h₁ : Nat.card l₁ = 1920) : Sylow 2 Extension :=
  (IsPGroup.of_card (n := 8) card_outerS).toSylow (by rw [outerS_index h₁]; decide)

@[simp] theorem outerSylow_coe (h₁ : Nat.card l₁ = 1920) :
    (outerSylow h₁ : Subgroup Extension) = outerS := rfl

@[simp] theorem card_outerSylow (h₁ : Nat.card l₁ = 1920) : Nat.card (outerSylow h₁) = 256 :=
  card_outerS

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
