module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.ImageGeneration
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Generation

/-!
# Binary recognition and generation in G.2.3(1–2)

The actual natural action identifies LT/O₂(LT) with S₃. Its two
original conjugate U-images generate it, and the two-residual condition
on L lifts that generation to I=LU. The restricted star map then gives
I/O₂(I)≃S₃, with its literal kernel and quotient-map compatibility.
The core normalizes U, and |U:U∩O₂(I)|=2.

`binary_source_recognition` gives clauses (1–2), including the Sylow
image and subgroup product. `binary_source_inputs` supplies exactly
the four remaining inputs of `binary_source_clauses_three_to_seven`.
U≤T is the authorized preceding G.2.2 conclusion. No internal-conjugacy,
generation, quotient-recognition, or core-normalization premise remains.

Source: Aschbacher–Smith, G.2.3, printed pp.333–334.
-/

@[expose] public section
open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

/-- The original two conjugates generate the entire literal star quotient. -/
theorem binary_source_star_generation (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    D.star (D.I g) = ⊤ :=
  binary_star_I_eq_top h.toBaseHypothesis b hUT g hgL hgN
    (binaryStarEquiv h.toBaseHypothesis b hUT)

/-- Clauses (1–2), with an actual equivalence, the literal Sylow image,
and both join and subgroup-product interpretations of LU. -/
theorem binary_source_recognition (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    Nonempty ((D.star D.L ⊔ D.star D.U : Subgroup D.Star) ≃* Equiv.Perm (Fin 3)) ∧
      (∃ P : Sylow 2 (D.star D.L ⊔ D.star D.U : Subgroup D.Star),
        (P : Subgroup (D.star D.L ⊔ D.star D.U : Subgroup D.Star)).map
          (D.star D.L ⊔ D.star D.U).subtype = D.star D.U) ∧
      D.I g = D.L ⊔ D.U ∧ (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) := by
  let e := binaryStarEquiv h.toBaseHypothesis b hUT
  have hi := binary_source_star_generation h b hUT g hgL hgN
  have he : D.star (D.I g) = D.star (D.L ⊔ D.U) := by
    rw [hi, binary_star_sup _ _ le_sup_left (hUT.trans le_sup_right),
      binary_star_join_eq_top hUT g hgL hi]
  exact ⟨⟨binaryStarJoinEquiv hUT g hgL e hi⟩,
    binary_star_U_sylow h.toBaseHypothesis b hUT g hgL e hi,
    binary_I_eq_join_of_star_eq h.toBaseHypothesis hUT g hgL he,
    binary_I_product_of_star_eq h.toBaseHypothesis hUT g hgL he⟩

/-- The kernel of the restricted original star map is exactly O₂(I). -/
theorem binary_source_star_kernel (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL)).ker = pCore 2 (D.I g) :=
  binary_I_star_kernel hUT g hgL (binaryStarEquiv h.toBaseHypothesis b hUT)
    (binary_source_star_generation h b hUT g hgL hgN)

/-- The source quotient equivalence is constructed from the original star map. -/
noncomputable def binarySourceCoreEquiv (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* Equiv.Perm (Fin 3) :=
  binaryCoreQuotientEquiv hUT g hgL (binaryStarEquiv h.toBaseHypothesis b hUT)
    (binary_source_star_generation h b hUT g hgL hgN)

/-- Compatibility with both the original star quotient and its natural action. -/
theorem binarySourceCoreEquiv_apply (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) (x : D.I g) :
    binarySourceCoreEquiv h b hUT g hgL hgN (QuotientGroup.mk' (pCore 2 (D.I g)) x) =
      binaryStarEquiv h.toBaseHypothesis b hUT
        (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL) x) := rfl

/-- The four formerly missing premises of the source clauses (3–7).
The original moving g belongs to I as a consequence of the proved equality. -/
theorem binary_source_inputs (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    D.I g = D.L ⊔ D.U ∧
      Nonempty ((D.I g ⧸ pCore 2 (D.I g)) ≃* Equiv.Perm (Fin 3)) ∧
      D.S g ≤ normalizer (D.U : Set G) ∧ (D.W g).relIndex D.U = 2 ∧ g ∈ D.I g := by
  have hi := binary_source_star_generation h b hUT g hgL hgN
  have hI := (binary_source_recognition h b hUT g hgL hgN).2.2.1
  exact ⟨hI, ⟨binarySourceCoreEquiv h b hUT g hgL hgN⟩,
    binary_S_normalizes_U h.toBaseHypothesis hUT g hgL
      (binaryStarEquiv h.toBaseHypothesis b hUT) hi,
    binary_W_index h.toBaseHypothesis b hUT g hgL
      (binaryStarEquiv h.toBaseHypothesis b hUT) hi,
    hI ▸ mem_sup_left hgL⟩

end CFSG.Quasithin.ChapterG.Section02.Setup
