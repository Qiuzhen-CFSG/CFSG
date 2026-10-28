module

public import Theory.Representation.MathieuCodeRestriction.Duality
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Two-subset cocode vectors and cyclic duality transport

The source O₂ sets are literal images of two-subsets in the native cocode:
all pairs for M₂₄, and pairs containing native point zero for M₂₃. Coordinate
permutations preserve these sets. The certified Golay rows separate points;
self-orthogonality therefore shows that none of these pair images is zero.

The genuine code–cocode dualities also identify displacement ranks, hence
fixed-space dimensions, for every cyclic subgroup. In particular, odd-prime
numerical bounds proved for the cocode transfer to the actual code.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.13.1
(printed p.395) and the orbit conventions preceding H.15.1 (printed p.398),
used in H.15.7 (printed pp.401–402). The odd-prime spectrum, normalizer
identification and orbit-avoiding bounds are separate proof obligations.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu
open scoped BigOperators Pointwise
open Representation.BinaryOffender
namespace MathieuCode

/-- The even word of an actual two-subset of the native twenty-four points. -/
def twoSubsetCore (B : Finset (Fin 24)) (hB : B.card = 2) : Core :=
  ⟨wordOfSet B, by
    classical
    change (∑ i : Fin 24, if i ∈ B then (1 : ZMod 2) else 0) = 0
    simp [hB]⟩

/-- The image of a two-subset in the literal cocode quotient. -/
def twoSubsetClass (B : Finset (Fin 24)) (hB : B.card = 2) : Cocode :=
  codeInCore.mkQ (twoSubsetCore B hB)

/-- The source weight-two orbit for M₂₄, defined by actual two-subset images. -/
def cocodeO2 : Set Cocode :=
  {v | ∃ (B : Finset (Fin 24)) (hB : B.card = 2), v = twoSubsetClass B hB}

/-- The source weight-two orbit for M₂₃: two-subsets containing native point zero. -/
def m23CocodeO2 : Set Cocode :=
  {v | ∃ (B : Finset (Fin 24)) (hB : B.card = 2),
    (0 : Fin 24) ∈ B ∧ v = twoSubsetClass B hB}

theorem m23CocodeO2_subset : m23CocodeO2 ⊆ cocodeO2 := by
  rintro v ⟨B, hB, _, rfl⟩
  exact ⟨B, hB, rfl⟩

theorem twoSubsetClass_action (g : M24) (B : Finset (Fin 24)) (hB : B.card = 2) :
    cocodeRepresentation g (twoSubsetClass B hB) =
      twoSubsetClass (g.val • B) (by simpa using hB) := by
  change codeInCore.mkQ (coreRepresentation g (twoSubsetCore B hB)) = _
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  exact permute_wordOfSet g.val B

theorem cocodeO2_invariant (g : M24) {v : Cocode} (hv : v ∈ cocodeO2) :
    cocodeRepresentation g v ∈ cocodeO2 := by
  obtain ⟨B, hB, rfl⟩ := hv
  exact ⟨g.val • B, by simpa using hB, twoSubsetClass_action g B hB⟩

theorem m23CocodeO2_invariant (g : M23) {v : Cocode} (hv : v ∈ m23CocodeO2) :
    m23CocodeRepresentation g v ∈ m23CocodeO2 := by
  obtain ⟨B, hB, h0, rfl⟩ := hv
  refine ⟨(pointEmbedding g).val • B, by simpa using hB, ?_,
    twoSubsetClass_action (pointEmbedding g) B hB⟩
  rw [← pointEmbedding_fixed g]
  exact Finset.smul_mem_smul_finset h0

private theorem rows_separate_points :
    ∀ i j : Fin 24, i ≠ j → ∃ k : Fin 12, row k i ≠ row k j := by
  decide +kernel

private theorem wordOfSet_pair (i j : Fin 24) (hij : i ≠ j) :
    wordOfSet {i, j} = Pi.single i 1 + Pi.single j 1 := by
  ext k
  by_cases hi : k = i
  · subst k; simp [wordOfSet, hij]
  · by_cases hj : k = j
    · subst k; simp [wordOfSet, hi]
    · simp [wordOfSet, hi, hj]

theorem twoSubsetClass_ne_zero (B : Finset (Fin 24)) (hB : B.card = 2) :
    twoSubsetClass B hB ≠ 0 := by
  intro hz
  have hb : wordOfSet B ∈ golay := (Submodule.Quotient.mk_eq_zero codeInCore).mp hz
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hB
  obtain ⟨k, hk⟩ := rows_separate_points i j hij
  have he := golay_le_orthogonal hb (row k) (row_mem k)
  rw [wordOfSet_pair i j hij] at he
  have hs : row k i + row k j = 0 := by
    simpa [dotForm, dotProductBilin, dotProduct_add, dotProduct_single] using he
  exact hk (by simpa only [ZMod.neg_eq_self_mod_two] using eq_neg_of_add_eq_zero_left hs)

theorem zero_not_mem_cocodeO2 : (0 : Cocode) ∉ cocodeO2 := by
  rintro ⟨B, hB, he⟩
  exact twoSubsetClass_ne_zero B hB he.symm

theorem zero_not_mem_m23CocodeO2 : (0 : Cocode) ∉ m23CocodeO2 :=
  fun h => zero_not_mem_cocodeO2 (m23CocodeO2_subset h)

/-- Duality preserves the displacement of every cyclic actor. -/
theorem code_cocode_fixedCodim_zpowers (g : M24) :
    fixedCodim codeRepresentation (Subgroup.zpowers g) =
      fixedCodim cocodeRepresentation (Subgroup.zpowers g) := by
  calc
    _ = fixedCodim cocodeRepresentation.dual (Subgroup.zpowers g) :=
      OddTransport.fixedCodim_eq_of_equivariant _ _ codeDuality.toLinearEquiv
        (fun a v => LinearMap.congr_fun (codeDuality.isIntertwining' a) v) _
    _ = _ := fixedCodim_zpowers_dual _ _

theorem m23_code_cocode_fixedCodim_zpowers (g : M23) :
    fixedCodim m23CodeRepresentation (Subgroup.zpowers g) =
      fixedCodim m23CocodeRepresentation (Subgroup.zpowers g) := by
  calc
    _ = fixedCodim m23CocodeRepresentation.dual (Subgroup.zpowers g) :=
      OddTransport.fixedCodim_eq_of_equivariant _ _ m23CodeDuality.toLinearEquiv
        (fun a v => LinearMap.congr_fun (m23CodeDuality.isIntertwining' a) v) _
    _ = _ := fixedCodim_zpowers_dual _ _

theorem code_cocode_fixedCodim_cyclic (D : Subgroup M24) [IsCyclic D] :
    fixedCodim codeRepresentation D = fixedCodim cocodeRepresentation D := by
  obtain ⟨g, rfl⟩ := D.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  exact code_cocode_fixedCodim_zpowers g

theorem m23_code_cocode_fixedCodim_cyclic (D : Subgroup M23) [IsCyclic D] :
    fixedCodim m23CodeRepresentation D = fixedCodim m23CocodeRepresentation D := by
  obtain ⟨g, rfl⟩ := D.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  exact m23_code_cocode_fixedCodim_zpowers g

theorem code_cocode_fixed_finrank_cyclic (D : Subgroup M24) [IsCyclic D] :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation D) =
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) := by
  have hc := fixedCodim_add_finrank codeRepresentation D
  have ht := fixedCodim_add_finrank cocodeRepresentation D
  rw [finrank_code] at hc
  rw [finrank_cocode] at ht
  have := code_cocode_fixedCodim_cyclic D
  omega

theorem m23_code_cocode_fixed_finrank_cyclic (D : Subgroup M23) [IsCyclic D] :
    Module.finrank (ZMod 2) (fixedSpace m23CodeRepresentation D) =
      Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D) := by
  have hc := fixedCodim_add_finrank m23CodeRepresentation D
  have ht := fixedCodim_add_finrank m23CocodeRepresentation D
  rw [finrank_code] at hc
  rw [finrank_cocode] at ht
  have := m23_code_cocode_fixedCodim_cyclic D
  omega
end MathieuCode
