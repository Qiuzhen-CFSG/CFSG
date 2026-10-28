module

public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.WeightArithmetic
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.FixedLine
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.Cyclicity
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Simplicity and distinctness of concrete Suzuki Frobenius tensors

A nonzero invariant subspace contains a nonzero vector fixed by the actual
root two-group. If its fixed space is the specified highest line and the
highest vector is cyclic, the tensor is irreducible. An actual intertwiner
preserves that line and its torus character; binary support recovery and the
dimension comparison then imply distinctness, including empty and full support.

The root norm calculation proves highest-line uniqueness, and the concrete
symplectic pairing proves cyclicity. These discharge the geometric premises
below for every support and every extension of the defining field, including
empty and full support and `m = 1`. Algebraic closure is unnecessary. The
independent odd-order class bound is still needed for tensor exhaustion.

Sources: GLS3, 2.8.2--2.8.8; Guralnick--Malle, *Classification of 2F-modules,
II*, §3.1, equation (3.2), and Lemma 8.3.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural
variable {m : ℕ} {K : Type*} [Field K] [Algebra (F m) K]

/-- The actual root two-group supplies the fixed vector needed for simplicity.
Only fixed-line uniqueness and cyclicity remain as geometric premises. -/
theorem tensorRep_irreducible_of_fixedLine_and_span [CharP K 2]
    (hm : 1 ≤ m) (I : Support m)
    (hfixed : ∀ v : TensorSpace m K I,
      (∀ g ∈ SuzukiRootSubgroup m, tensorRep m K I g v = v) →
        ∃ c : K, v = c • tensorHighestVector m K I)
    (hspan : Submodule.span K (Set.range fun g : SuzukiMatrixGroup m =>
      tensorRep m K I g (tensorHighestVector m K I)) = ⊤) :
    IsIrreducible (tensorRep m K I) := by
  let : Nontrivial (TensorSpace m K I) :=
    ⟨⟨tensorHighestVector m K I, 0, tensorHighestVector_ne_zero m K I⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  have hp : IsPGroup (ringChar K) (SuzukiRootSubgroup m) := by
    rw [ringChar.eq K 2]
    exact suzukiRootSubgroup_isPGroup m (by omega)
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (F := K) (G := SuzukiRootSubgroup m) (V := S.toSubmodule)
    (by rw [ringChar.eq K 2]; decide) hp
    (S.toRepresentation.comp (SuzukiRootSubgroup m).subtype)
  obtain ⟨c, hc⟩ := hfixed v.val (fun g hg => congrArg Subtype.val (hfix ⟨g, hg⟩))
  have hc0 : c ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    change v.val = (0 : TensorSpace m K I)
    simpa only [h, zero_smul] using hc
  have hseed : tensorHighestVector m K I ∈ S := by
    apply (S.toSubmodule.smul_mem_iff hc0).mp
    rw [← hc]
    exact v.property
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact S.apply_mem_toSubmodule g hseed

private theorem tensorEquiv_apply_action {I J : Support m}
    (e : (tensorRep m K I).Equiv (tensorRep m K J)) (g : SuzukiMatrixGroup m)
    (v : TensorSpace m K I) : e (tensorRep m K I g v) = tensorRep m K J g (e v) :=
  LinearMap.congr_fun (e.isIntertwining' g) v

/-- Highest-line uniqueness in the target forces an intertwiner to map the
specified highest vector to a nonzero scalar multiple of the target vector. -/
theorem tensorEquiv_highestVector_scalar {I J : Support m}
    (hfixed : ∀ v : TensorSpace m K J,
      (∀ g ∈ SuzukiRootSubgroup m, tensorRep m K J g v = v) →
        ∃ c : K, v = c • tensorHighestVector m K J)
    (e : (tensorRep m K I).Equiv (tensorRep m K J)) :
    ∃ c : K, c ≠ 0 ∧ e (tensorHighestVector m K I) = c • tensorHighestVector m K J := by
  obtain ⟨c, hc⟩ := hfixed (e (tensorHighestVector m K I)) (by
    intro g hg
    rw [← tensorEquiv_apply_action, tensorHighestVector_fixed_root m K I g hg])
  refine ⟨c, ?_, hc⟩
  intro hc0
  rw [hc0, zero_smul] at hc
  exact tensorHighestVector_ne_zero m K I (e.toLinearEquiv.map_eq_zero_iff.mp hc)

/-- Literal intertwining preserves the highest-line character of the split torus. -/
theorem tensorEquiv_weight_characters {I J : Support m}
    (hfixed : ∀ v : TensorSpace m K J,
      (∀ g ∈ SuzukiRootSubgroup m, tensorRep m K J g v = v) →
        ∃ c : K, v = c • tensorHighestVector m K J)
    (e : (tensorRep m K I).Equiv (tensorRep m K J)) (t : (F m)ˣ) :
    t.val ^ ((1 + 2 ^ m) * supportWeight I) =
      t.val ^ ((1 + 2 ^ m) * supportWeight J) := by
  obtain ⟨c, hc0, hc⟩ := tensorEquiv_highestVector_scalar hfixed e
  have hh := tensorEquiv_apply_action e (highestTorus m t) (tensorHighestVector m K I)
  rw [tensorHighestVector_torus, map_smul, hc, map_smul,
    tensorHighestVector_torus, smul_smul, smul_smul] at hh
  have hs := smul_left_injective K (tensorHighestVector_ne_zero m K J) hh
  have he := mul_right_cancel₀ hc0 (by simpa only [mul_comm c] using hs)
  apply (algebraMap (F m) K).injective
  simpa only [map_pow] using he

/-- Fixed-line uniqueness alone implies distinctness of the concrete tensors.
Dimension distinguishes the empty and full supports with the same character. -/
theorem tensorRep_equiv_imp_eq_of_fixedLine
    (hfixed : ∀ (I : Support m) (v : TensorSpace m K I),
      (∀ g ∈ SuzukiRootSubgroup m, tensorRep m K I g v = v) →
        ∃ c : K, v = c • tensorHighestVector m K I)
    {I J : Support m} (he : Nonempty ((tensorRep m K I).Equiv (tensorRep m K J))) :
    I = J := by
  obtain ⟨e⟩ := he
  exact support_eq_of_weight_characters m (support_card_eq_of_tensorRep_equiv e)
    (tensorEquiv_weight_characters (hfixed J) e)

/-- The specified highest vector generates the whole concrete tensor, over
every extension of the defining field and for every support. -/
theorem tensorHighestVector_orbit_span (hm : 1 ≤ m) (I : Support m) :
    Submodule.span K (Set.range fun g : SuzukiMatrixGroup m =>
      tensorRep m K I g (tensorHighestVector m K I)) = ⊤ :=
  tensorHighestVector_orbit_span_of_fixedLine hm I (tensor_fixed_root m hm K I)

/-- All concrete Suzuki Frobenius tensors are irreducible over every extension
of the defining field, including the empty and full supports. -/
theorem tensorRep_irreducible (hm : 1 ≤ m) (I : Support m) :
    IsIrreducible (tensorRep m K I) := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (F m) K).injective 2
  exact tensorRep_irreducible_of_fixedLine_and_span hm I
    (tensor_fixed_root m hm K I) (tensorHighestVector_orbit_span hm I)

/-- An actual equivalence of concrete Suzuki Frobenius tensors determines
their supports, including the empty/full torus-character collision. -/
theorem tensorRep_equiv_imp_eq (hm : 1 ≤ m) {I J : Support m}
    (he : Nonempty ((tensorRep m K I).Equiv (tensorRep m K J))) : I = J :=
  tensorRep_equiv_imp_eq_of_fixedLine (tensor_fixed_root m hm K) he

end Representation.SuzukiSmallDegree
