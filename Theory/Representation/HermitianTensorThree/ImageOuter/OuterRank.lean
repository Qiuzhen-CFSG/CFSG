module

public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Transport
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Coefficients
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Descent

/-!
# Rank assembly for the Hermitian tensor normalizer

An elementary subgroup inside the image has rank at most 4n. For one
containing an outer involution, normalizer conjugacy carries its intersection
with the image into the marked centralizer, of rank 2n. An elementary outer
index at most two then gives rank at most 2n+1, hence at most 4n.
The source equation L = M∞ puts M inside this same literal normalizer.

Normalizer coverage determines the coefficient of every outer involution as
the quadratic Frobenius. Matrix descent then conjugates it to the actual
field swap by an element of the full binary normalizer. The same coverage
bounds the elementary outer index by two, retaining fixed-field scalars and
inner-diagonal cosets. This discharges the fusion and index premises of the
rank argument below. Only coverage and the marked-centralizer equivalence
remain inputs to the source rank theorem; their producers belong to the
normalizer and field-section developments.

Source: Aschbacher–Smith, H.4.4(6) and m₂ = 4n, printed pp.381–382;
the source overgroup hypotheses are on printed p.377.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.OuterRank
open Subgroup Theory.GroupTheory
variable (n : ℕ) [NeZero n]

/-- The outer elementary branch: the intersection embeds in the actual
marked centralizer, and its index contributes at most one generator. -/
theorem elementary_outer_twoRank_le
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n)))
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hiIndex : (binaryImage n).relIndex A ≤ 2)
    (i : Space n ≃ₗ[ZMod 2] Space n) (hiA : i ∈ A)
    (c : Space n ≃ₗ[ZMod 2] Space n) (hc : c ∈ binaryNormalizer n)
    (hi : MulAut.conj c i = fieldSwapBinary n) :
    primeRank 2 A ≤ 2 * n + 1 := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let C := (binaryImage n).subgroupOf A
  let j : C →* ↥(binaryImage n ⊓ centralizer ({i} : Set (Space n ≃ₗ[ZMod 2] Space n))) := {
    toFun x := ⟨x.val.val, x.property, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm x.val (⟨i, hiA⟩ : A)))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    have hh : x.val.val = y.val.val :=
      congrArg (fun g : ↥(binaryImage n ⊓ centralizer ({i} : Set (Space n ≃ₗ[ZMod 2] Space n))) => g.val) h
    exact Subtype.ext (Subtype.ext hh)
  have hC : primeRank 2 C ≤ 2 * n := by
    have hb := primeRank_le_of_injective 2 j hj
    rw [primeRank_equiv 2 (imageCentralizerEquivOfConj n i c hc hi),
      markedCentralizer_twoRank n hK] at hb
    exact hb
  have hb := primeRank_le_add_of_index_le (p := 2) (n := 1) C (by
    simpa only [pow_one, Subgroup.relIndex] using hiIndex)
  exact hb.trans (Nat.add_le_add_right hC 1)

/-- Combining the inner and outer branches in the full binary normalizer. -/
theorem normalizer_twoRank_le_of_fusion_index
    (hFusion : ∀ i ∈ binaryNormalizer n, orderOf i = 2 → i ∉ binaryImage n →
      ∃ c ∈ binaryNormalizer n, MulAut.conj c i = fieldSwapBinary n)
    (hIndex : ∀ A : Subgroup (Space n ≃ₗ[ZMod 2] Space n), IsElementaryAbelian 2 A →
      A ≤ binaryNormalizer n → (binaryImage n).relIndex A ≤ 2)
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n))) :
    primeRank 2 (binaryNormalizer n) ≤ 4 * n := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro B hB
  let := hB
  let A := B.map (binaryNormalizer n).subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  have hAN : A ≤ binaryNormalizer n := map_subtype_le B
  have hAr : primeRank 2 A ≤ 4 * n := by
    by_cases hAL : A ≤ binaryImage n
    · exact (primeRank_le_of_injective 2 (inclusion hAL)
        (inclusion_injective hAL)).trans (binaryImage_twoRank n).le
    · obtain ⟨i, hiA, hiL⟩ := SetLike.not_le_iff_exists.mp hAL
      have hi2 : orderOf i = 2 := orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (A := A) i hiA)
        (fun h => hiL (h ▸ (binaryImage n).one_mem))
      obtain ⟨c, hc, hci⟩ := hFusion i (hAN hiA) hi2 hiL
      have hb := elementary_outer_twoRank_le n hK A (hIndex A inferInstance hAN) i hiA c hc hci
      have hn := Nat.pos_of_ne_zero (NeZero.ne n)
      omega
  have hrB : primeRank 2 B ≤ 4 * n := by
    rw [primeRank_equiv 2 (B.equivMapOfInjective _ (binaryNormalizer n).subtype_injective)]
    exact hAr
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup B) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 B) x.val)) }
  have hb := (primeRank_le_iff_elementary_card_le B).mp hrB ⊤ ht
  simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hb

/-- Application to M with its faithful binary action and its actual residual. -/
theorem sourceOvergroup_twoRank_le_of_fusion_index
    (hFusion : ∀ i ∈ binaryNormalizer n, orderOf i = 2 → i ∉ binaryImage n →
      ∃ c ∈ binaryNormalizer n, MulAut.conj c i = fieldSwapBinary n)
    (hIndex : ∀ A : Subgroup (Space n ≃ₗ[ZMod 2] Space n), IsElementaryAbelian 2 A →
      A ≤ binaryNormalizer n → (binaryImage n).relIndex A ≤ 2)
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n)))
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M) :
    primeRank 2 M ≤ 4 * n := by
  exact (primeRank_le_of_injective 2 (inclusion (sourceOvergroup_le_normalizer n M hM))
    (inclusion_injective _)).trans (normalizer_twoRank_le_of_fusion_index n hFusion hIndex hK)

/-- The image attains the bound in every source overgroup under the supplied
fusion and outer-index statements. -/
theorem sourceOvergroup_twoRank_eq_of_fusion_index
    (hFusion : ∀ i ∈ binaryNormalizer n, orderOf i = 2 → i ∉ binaryImage n →
      ∃ c ∈ binaryNormalizer n, MulAut.conj c i = fieldSwapBinary n)
    (hIndex : ∀ A : Subgroup (Space n ≃ₗ[ZMod 2] Space n), IsElementaryAbelian 2 A →
      A ≤ binaryNormalizer n → (binaryImage n).relIndex A ≤ 2)
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n)))
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M) :
    primeRank 2 M = 4 * n :=
  le_antisymm (sourceOvergroup_twoRank_le_of_fusion_index n hFusion hIndex hK M hM)
    (sourceOvergroup_twoRank_ge n M hM)

/-- Every outer involution in the full binary normalizer is conjugate to the
actual field swap. The conjugator may retain an inner-diagonal factor. -/
theorem outer_involution_conjugate (hCoverage : NormalizerCoverage n)
    (i : Space n ≃ₗ[ZMod 2] Space n) (hiN : i ∈ binaryNormalizer n)
    (hi2 : orderOf i = 2) (hiL : i ∉ binaryImage n) :
    ∃ c ∈ binaryNormalizer n, MulAut.conj c i = fieldSwapBinary n := by
  obtain ⟨g, hg⟩ := Coefficients.outer_involution_expression n hCoverage i hiN hi2 hiL
  have hi : i ^ 2 = 1 := by simpa only [hi2] using pow_orderOf_eq_one i
  exact exists_conj_fieldSwapBinary_of_sigma_expression n i hi g hg

/-- Applying outer fusion to the literal source group transports M together
with its residual. The marked swap belongs to the transported group, and
`overgroupAction_conj` intertwines the two faithful binary actions. -/
theorem source_outer_involution_transport_of_coverage (hCoverage : NormalizerCoverage n)
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (i : M) (hi : orderOf i = 2) (hiL : i.val ∉ binaryImage n) :
    ∃ c ∈ binaryNormalizer n,
      MulAut.conj c i.val = fieldSwapBinary n ∧
      SourceOvergroup n (M.map (MulAut.conj c).toMonoidHom) ∧
      fieldSwapBinary n ∈ M.map (MulAut.conj c).toMonoidHom :=
  source_outer_involution_transport n (outer_involution_conjugate n hCoverage) M hM i hi hiL

/-- The full binary normalizer has two-rank at most 4n. The only structural
inputs are semilinear coverage and the literal marked-centralizer model. -/
theorem normalizer_twoRank_le (hCoverage : NormalizerCoverage n)
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n))) :
    primeRank 2 (binaryNormalizer n) ≤ 4 * n :=
  normalizer_twoRank_le_of_fusion_index n (outer_involution_conjugate n hCoverage)
    (Coefficients.elementary_relIndex_le_two n hCoverage) hK

/-- The source rank bound, preserving the faithful binary action and the
source equation L = M∞. Fusion and the outer index are now discharged. -/
theorem sourceOvergroup_twoRank_le (hCoverage : NormalizerCoverage n)
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n)))
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M) :
    primeRank 2 M ≤ 4 * n :=
  sourceOvergroup_twoRank_le_of_fusion_index n (outer_involution_conjugate n hCoverage)
    (Coefficients.elementary_relIndex_le_two n hCoverage) hK M hM

/-- The image supplies equality in the source rank bound m₂(M) = 4n. -/
theorem sourceOvergroup_twoRank_eq (hCoverage : NormalizerCoverage n)
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n)))
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M) :
    primeRank 2 M = 4 * n :=
  le_antisymm (sourceOvergroup_twoRank_le n hCoverage hK M hM)
    (sourceOvergroup_twoRank_ge n M hM)

end Representation.HermitianTensorThree.ImageOuter.OuterRank
