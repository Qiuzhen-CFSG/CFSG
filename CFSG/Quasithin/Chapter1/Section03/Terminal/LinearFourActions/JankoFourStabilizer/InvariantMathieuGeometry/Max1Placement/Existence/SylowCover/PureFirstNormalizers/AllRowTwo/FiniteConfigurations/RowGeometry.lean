module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.Data

/-!
# Exact membership, order and purity of the literal native rows

The certified kernel multiplication law closes each finite mask list. Its
image is therefore already a subgroup, so the definition by closure has
exactly the advertised elements. Injectivity of the actual kernel words gives
the orders and distinctness. Containment in the previously proved elementary
marked intersection gives elementary abelian structure. The existing native
conjugacy forest, rather than a rank-only diagnostic, proves ambient purity.

This certifies all sixteen eights and ten sixteens as literal pure elementary
subgroups with both actual marked points. Excluding the native pair in every
row and exhausting the eligible marked subgroups are separate obligations.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), Section 2.1, pp.488--489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open MarkedIntersection
open Janko4.Cardinality.LocalInvolutionCensus
open Janko4.Cardinality.LocalInvolutionCensus.Coordinates
open Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
set_option Elab.async false
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
attribute [local instance 2000] Finset.decidableDforallFinset
attribute [local instance 2000] Finset.decidableExistsAndFinset

private theorem masks_zero : ∀ i, (0 : Fin 8192) ∈ rowMasks i := by decide +kernel

private theorem masks_coordinates : ∀ i, ∀ m ∈ rowMasks i,
    ∃ j : Fin 128, coordinate j = m := by decide +kernel

set_option maxRecDepth 10000 in
private theorem masks_product : ∀ i, ∀ m ∈ rowMasks i, ∀ n ∈ rowMasks i,
    (⟨maskMultiply m.val n.val % 8192, Nat.mod_lt _ (by decide)⟩ : Fin 8192) ∈ rowMasks i := by
  decide +kernel

private theorem masks_mul (i : Fin 26) (m : Fin 8192) (hm : m ∈ rowMasks i)
    (n : Fin 8192) (hn : n ∈ rowMasks i) :
    ∃ k ∈ rowMasks i, maskMultiply m.val n.val = k.val := by
  refine ⟨⟨maskMultiply m.val n.val % 8192, Nat.mod_lt _ (by decide)⟩,
    masks_product i m hm n hn,?_⟩
  symm
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow (n := 13) (Nat.xor_lt_two_pow m.isLt n.isLt)
  cases correction m.val n.val <;> decide

theorem nativeWord_zero : nativeWord 0 = 1 := by
  change (kernelProduct 0 : Model) = 1
  have h : kernelProduct 0 = 1 := by simp [kernelProduct]
  exact congrArg Subtype.val h

theorem nativeWord_injective : Function.Injective nativeWord := by
  intro m n h
  exact kernelProduct_injective (Subtype.ext h)

theorem nativeWord_mem_intersection (i : Fin 26) (m : Fin 8192) (hm : m ∈ rowMasks i) :
    nativeWord m ∈ markedIntersection := by
  obtain ⟨j,hj⟩ := masks_coordinates i m hm
  exact (mem_markedIntersection_iff _).mpr ⟨j,congrArg nativeWord hj⟩

theorem row_le_markedIntersection (i : Fin 26) : row i ≤ markedIntersection := by
  apply (closure_le _).mpr
  rintro _ ⟨m,hm,rfl⟩
  exact nativeWord_mem_intersection i m hm

theorem row_elementary (i : Fin 26) : IsElementaryAbelian 2 (row i) := by
  let := markedIntersection_elementary
  exact IsElementaryAbelian.of_le (row_le_markedIntersection i)

/-- The generating mask list is already a subgroup, so these are exact
membership coordinates, not just a list of generators. -/
theorem mem_row_iff (i : Fin 26) (x : Model) : x ∈ row i ↔
    ∃ m ∈ rowMasks i, nativeWord m = x := by
  let S : Subgroup Model := {
    carrier := nativeWord '' (rowMasks i : Set (Fin 8192))
    one_mem' := ⟨0,masks_zero i,nativeWord_zero⟩
    mul_mem' := by
      rintro _ _ ⟨m,hm,rfl⟩ ⟨n,hn,rfl⟩
      obtain ⟨k,hk,he⟩ := masks_mul i m hm n hn
      refine ⟨k,hk,?_⟩
      change ((maskProduct kernelFactor k.val : sourceSubgroup) : Model) =
        ((maskProduct kernelFactor m.val : sourceSubgroup) : Model) *
        ((maskProduct kernelFactor n.val : sourceSubgroup) : Model)
      rw [← he,source_mask_multiply]
      rfl
    inv_mem' := by
      rintro _ ⟨m,hm,rfl⟩
      refine ⟨m,hm,?_⟩
      let := markedIntersection_elementary
      have hsq := elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (nativeWord m) (nativeWord_mem_intersection i m hm)
      exact (inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq)).symm
  }
  have he : row i = S := closure_eq S
  rw [he]
  rfl

theorem nativeWord_mem_row_iff (i : Fin 26) (m : Fin 8192) :
    nativeWord m ∈ row i ↔ m ∈ rowMasks i := by
  rw [mem_row_iff]
  constructor
  · rintro ⟨n,hn,he⟩
    exact nativeWord_injective he ▸ hn
  · exact fun hm => ⟨m,hm,rfl⟩

theorem row_card (i : Fin 26) : Nat.card (row i) = if i.val < 16 then 8 else 16 := by
  let f : {m // m ∈ rowMasks i} → row i :=
    fun m => ⟨nativeWord m.val,(nativeWord_mem_row_iff i m.val).mpr m.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro m n h
      apply Subtype.ext
      exact nativeWord_injective (congrArg (fun x : row i => (x : Model)) h)
    · intro x
      obtain ⟨m,hm,hx⟩ := (mem_row_iff i x.val).mp x.property
      exact ⟨⟨m,hm⟩,Subtype.ext hx⟩
  have hc : ∀ i, (rowMasks i).card = if i.val < 16 then 8 else 16 := by decide +kernel
  calc
    Nat.card (row i) = Nat.card {m // m ∈ rowMasks i} :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = (rowMasks i).card := by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = _ := hc i

theorem row_le_iff (i j : Fin 26) : row i ≤ row j ↔ rowMasks i ⊆ rowMasks j := by
  constructor
  · intro h m hm
    exact (nativeWord_mem_row_iff j m).mp (h ((nativeWord_mem_row_iff i m).mpr hm))
  · intro h x hx
    obtain ⟨m,hm,rfl⟩ := (mem_row_iff i x).mp hx
    exact (nativeWord_mem_row_iff j m).mpr (h hm)

theorem row_injective : Function.Injective row := by
  intro i j he
  have hc : Function.Injective rowMasks := by decide +kernel
  apply hc
  exact Finset.Subset.antisymm ((row_le_iff i j).mp he.le) ((row_le_iff j i).mp he.ge)

theorem markedT_mem_row (i : Fin 26) : markedT ∈ row i := by
  have he : nativeWord 1 = markedT := by
    have hh : kernelProduct 1 = kernelFactor 0 := by
      change kernelFactor 0 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1)))))))))))) = _
      simp only [mul_one]
    change (kernelProduct 1 : Model) = OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.t
    rw [hh]
    exact coe_sourceSeed_sq
  rw [← he,nativeWord_mem_row_iff]
  have hc : ∀ i, (1 : Fin 8192) ∈ rowMasks i := by decide +kernel
  exact hc i

theorem markedP_mem_row (i : Fin 26) : markedP ∈ row i := by
  change nativeWord 6607 ∈ row i
  rw [nativeWord_mem_row_iff]
  have hc : ∀ i, (6607 : Fin 8192) ∈ rowMasks i := by decide +kernel
  exact hc i

private theorem listed_nativeWord_pure (m : Fin 8192)
    (hm : m ∈ masks 1 ∨ m ∈ masks 2) : IsConj a (nativeWord m) := by
  have help (k : Fin 11) (hk : k = 1 ∨ k = 2) (hm : m ∈ masks k) :
      IsConj a (nativeWord m) := by
    have hc := Forest.listed_isConj_of_edges (Forest.edges Cardinality.Thompson.max2_card.le) k m hm
    have hf : fiberIndex k = 0 := by rcases hk with rfl | rfl <;> rfl
    have he : sourceElement (fiberIndex k) m = kernelProduct m := by
      rw [hf,sourceElement]
      change kernelProduct m * 1 = kernelProduct m
      exact mul_one _
    rw [he] at hc
    have hl := eH.map_isConj (sourceSubgroupEquivLocal.toMonoidHom.map_isConj hc)
    simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,sourceEquiv_representative] at hl
    have ha : IsConj a (eH (representative k)) := by
      have hh := firstTarget_isConj_representative k
      rcases hk with rfl | rfl <;> exact hh
    apply (ha.trans hl).trans
    apply isConj_iff.mpr
    refine ⟨h,?_⟩
    rw [eH_sourceSubgroupEquivLocal]
    simp [nativeWord,mul_assoc]
  rcases hm with hm | hm
  · exact help 1 (Or.inl rfl) hm
  · exact help 2 (Or.inr rfl) hm

/-- Actual ambient conjugacy of every nonidentity element in every listed row. -/
theorem row_pure (i : Fin 26) : ∀ x ∈ row i, x ≠ 1 → IsConj a x := by
  intro x hx hx1
  obtain ⟨m,hm,rfl⟩ := (mem_row_iff i x).mp hx
  have hm0 : m ≠ 0 := fun he => hx1 (he ▸ nativeWord_zero)
  have hc : ∀ i, ∀ m ∈ rowMasks i, m ≠ 0 → m ∈ masks 1 ∨ m ∈ masks 2 := by decide +kernel
  exact listed_nativeWord_pure m (hc i m hm hm0)

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
