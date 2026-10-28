module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.FixedLine.SteinbergReduction
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.FixedLine.RestrictedEmbeddings
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.FixedLine.SteinbergNorm

/-!
# Highest-line assembly for the concrete G₂ Frobenius tensors

For every restricted word over a field of order `2^n`, the fixed space of the
actual positive unipotent group is the published highest line. This includes
the all-trivial word and every boundary weight, over any coefficient-field
extension.

The four normalized embeddings in `RestrictedEmbeddings` tensor injectively
into the full Steinberg word. `SteinbergNorm` proves that its literal norm over
all six field-valued root parameters has highest coefficient one. The regular
orbit argument and scalar extension in `SteinbergReduction` then give the
fixed line, without any simplicity, cyclicity or classification premise.

Source: GLS3, 2.8.6(a), 2.8.9 and 2.8.10(g), used in Aschbacher--Smith G.9.3(10),
`refs/quasithin.pdf`, printed pp.354, 356--357.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.G2.TensorClassification
open Restricted
variable (F : Type*) [Field F] [CharP F 2]
  (K : Type*) [Field K] [Algebra F K]

/-- Every vector in an all-trivial word is its normalized coefficient times the
actual highest vector, including the empty word. -/
theorem tensor_eq_highestCoefficient_smul_of_all_trivial {n : ℕ}
    (w : Fin n → Factor) (hw : ∀ i, w i = .trivial) (v : TensorSpace F K w) :
    v = tensorHighestCoefficient F K w v • tensorHighestVector F K w := by
  have hd : Module.finrank K (TensorSpace F K w) = 1 := by
    rw [finrank_tensorSpace]
    simp [hw, Factor.dimension]
  have ht : Submodule.span K {tensorHighestVector F K w} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton (tensorHighestVector_ne_zero F K w), hd]
  have hv : v ∈ Submodule.span K {tensorHighestVector F K w} := by rw [ht]; trivial
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  simp

variable [Finite F] [Fintype F]

/-- The two independent concrete inputs imply the requested highest line for
every word and every coefficient extension. Neither input assumes tensor
simplicity, cyclicity or classification. -/
theorem tensor_fixed_unipotent_of_steinberg_data
    (j : (a : Factor) → Space F a →ₗ[F] Space F .steinberg)
    (hinj : ∀ a, Function.Injective (j a))
    (hseed : ∀ a, j a (highestVector F a) = highestVector F .steinberg)
    (hact : ∀ a g, g ∈ (unipotent : Subgroup (Model F)) → ∀ v,
      j a (action F a g v) = action F .steinberg g (j a v))
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hnorm : FixedLine.steinbergNorm F n ≠ 0)
    (w : Fin n → Factor) (v : TensorSpace F K w)
    (hv : ∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) :
    ∃ c : K, v = c • tensorHighestVector F K w := by
  apply FixedLine.tensor_fixed_of_word_fixed F K w _ v hv
  intro x hx
  exact FixedLine.word_fixed_of_steinberg_data F j hinj hseed hact (List.ofFn w)
    (by simpa only [List.length_ofFn] using hF)
    (by rw [List.length_ofFn]; exact hnorm) x hx

omit [Fintype F] in
/-- Every unipotent-fixed vector in an actual G₂ Frobenius tensor lies on its
published highest line. All restricted words are allowed, including trivial
and boundary words; neither algebraic closure nor `n ≥ 2` is needed. -/
theorem tensor_fixed_unipotent {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (w : Fin n → Factor) (v : TensorSpace F K w)
    (hv : ∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) :
    ∃ c : K, v = c • tensorHighestVector F K w := by
  let : Fintype F := Fintype.ofFinite F
  exact tensor_fixed_unipotent_of_steinberg_data F K
    (FixedLine.RestrictedEmbeddings.embedding F)
    (FixedLine.RestrictedEmbeddings.embedding_injective F)
    (FixedLine.RestrictedEmbeddings.embedding_highestVector F)
    (FixedLine.RestrictedEmbeddings.embedding_intertwines F)
    hF (FixedLine.steinbergNorm_ne_zero F hF) w v hv

omit [Fintype F] in
/-- The scalar of a unipotent-fixed tensor is its normalized highest
coefficient. -/
theorem tensor_eq_highestCoefficient_smul_of_fixed_unipotent {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor) (v : TensorSpace F K w)
    (hv : ∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) :
    v = tensorHighestCoefficient F K w v • tensorHighestVector F K w := by
  obtain ⟨c, rfl⟩ := tensor_fixed_unipotent F K hF w v hv
  simp

omit [Fintype F] in
/-- The full fixed space of the actual unipotent action is exactly the
specified highest line. -/
theorem tensor_fixed_unipotent_iff {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (w : Fin n → Factor) (v : TensorSpace F K w) :
    (∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) ↔
      ∃ c : K, v = c • tensorHighestVector F K w := by
  constructor
  · exact tensor_fixed_unipotent F K hF w v
  · rintro ⟨c, rfl⟩ g hg
    rw [map_smul, tensorHighestVector_fixed_unipotent F K w g hg]

end Atlas.G2.TensorClassification
end
