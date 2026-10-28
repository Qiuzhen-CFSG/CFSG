module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces

/-!
# Native cubic witnesses and M₂₃ restriction transport

Conjugating the second native standard generator by the first fixes native
point zero and exactly six points in total. Its cyclic subgroup therefore
lies in the actual image of M₂₃. These are concrete order-three witnesses;
no Atlas class label or conjugacy-table convention is used.

Fixed spaces and displacements on M₂₃ are exactly those of the image under
`MathieuCode.pointEmbedding`. Used for the beta tables on printed p.396 of
Aschbacher–Smith and H.15.7, printed pp.401–402.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Representation.BinaryOffender
namespace MathieuCode

theorem m23_cocode_fixedSpace_eq_map (D : Subgroup M23) :
    fixedSpace m23CocodeRepresentation D =
      fixedSpace cocodeRepresentation (D.map pointEmbedding) := by
  ext v
  simp only [mem_fixedSpace_iff]
  constructor
  · intro hv g hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact hv a ha
  · intro hv a ha
    exact hv (pointEmbedding a) ⟨a, ha, rfl⟩

theorem m23_cocode_fixedCodim_eq_map (D : Subgroup M23) :
    fixedCodim m23CocodeRepresentation D =
      fixedCodim cocodeRepresentation (D.map pointEmbedding) := by
  unfold fixedCodim
  rw [m23_cocode_fixedSpace_eq_map]

def sixFixedCubic : M24 :=
  (⟨m24GeneratorA, m24GeneratorA_mem⟩ : M24) *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ * (⟨m24GeneratorA, m24GeneratorA_mem⟩ : M24)⁻¹

theorem sixFixedCubic_order : orderOf sixFixedCubic = 3 := by
  rw [← orderOf_injective M24.subtype Subtype.coe_injective]
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

theorem sixFixedCubic_fixes_zero : sixFixedCubic.val 0 = 0 := by decide +kernel

theorem sixFixedCubic_fixed_card :
    Nat.card (MulAction.fixedPoints (Subgroup.zpowers sixFixedCubic) (Fin 24)) = 6 := by
  have he : MulAction.fixedPoints (Subgroup.zpowers sixFixedCubic) (Fin 24) =
      {i : Fin 24 | sixFixedCubic.val i = i} := by
    ext i
    constructor
    · intro hi
      exact hi ⟨sixFixedCubic, Subgroup.mem_zpowers sixFixedCubic⟩
    · intro hi a
      exact smul_eq_self_of_mem_zpowers a.property hi
  rw [he, Nat.card_eq_fintype_card]
  decide +kernel

theorem exists_m24_cubic_six_fixed : ∃ D : Subgroup M24,
    Nat.card D = 3 ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) = 6 := by
  exact ⟨Subgroup.zpowers sixFixedCubic, (Nat.card_zpowers _).trans sixFixedCubic_order,
    sixFixedCubic_fixed_card⟩

theorem exists_m23_cubic_six_fixed : ∃ D : Subgroup M23,
    Nat.card D = 3 ∧ Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6 := by
  have hm : sixFixedCubic ∈ pointEmbedding.range := by
    rw [pointEmbedding_range]
    exact sixFixedCubic_fixes_zero
  obtain ⟨a, ha⟩ := hm
  refine ⟨Subgroup.zpowers a, ?_, ?_⟩
  · rw [Nat.card_zpowers, ← orderOf_injective pointEmbedding pointEmbedding_injective, ha]
    exact sixFixedCubic_order
  · rw [MonoidHom.map_zpowers, ha]
    exact sixFixedCubic_fixed_card
end MathieuCode
