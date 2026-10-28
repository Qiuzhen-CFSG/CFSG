module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs

/-!
# Conjugate spans in Section 13.5

The bound N_G(V₁) ∩ N_G(V₃) ≤ M forces V₃ < U_H for every member
of the literal H_z family outside M. In the A₅ branch, the same bound
and C_M(V₃) = C_M(V) allow F.9.4(3) to compare abelianness of U_H,
abelianness of V_H and V ≤ O₂(H).

The F.9 hypothesis, the normalizer bound of 13.5.5 and the natural-module
centralizer equality remain explicit earlier inputs. Their source
construction is required for the unconditional 13.5.9–10 and terminal
13.5.12 assembly. The family and both conjugate spans are the existing
literal constructions shared with the Section 13.8 consumers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.5 and 13.5.8–10, printed pp.916–918 (PDF pp.933–935).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05
variable {G : Type*} [Group G]

/-- The inference of 13.5.9 from the normalizer bound of 13.5.5. -/
theorem seed_lt_span
    (V₁ V₃ H M : Subgroup G)
    (hH : H ≤ normalizer (V₁ : Set G)) (hout : ¬ H ≤ M)
    (hbound : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M) :
    V₃ < conjugateSpanBy V₃ H := by
  refine lt_of_le_of_ne (le_conjugateSpanBy V₃ H) ?_
  intro he
  have hn := le_normalizer_conjugateSpanBy V₃ H
  rw [← he] at hn
  exact hout ((le_inf hH hn).trans hbound)

/-- Apply the preceding inference to the literal family H_z from 13.5.8. -/
theorem seed_lt_UH_of_mem_Hz
    (L₁ T V₁ V₃ M H : Subgroup G)
    (hH : H ∈ Section08.Source.Hz L₁ T (normalizer (V₁ : Set G)) M)
    (hbound : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M) :
    V₃ < Section08.Source.UH H V₃ :=
  seed_lt_span V₁ V₃ H M hH.2.1 hH.2.2 hbound

/-- F.9.4(3) yields all three equivalences in 13.5.10 once 13.5.7 and
C_M(V₃)=C_M(V) are supplied. Normalizers remain in the ambient group. -/
theorem a5_abelian_span_equivalences [Finite G]
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) (M : Subgroup G)
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hcentral : M ⊓ centralizer (D.Vplus : Set G) =
      M ⊓ centralizer (D.V : Set G)) :
    (IsMulCommutative D.UH ↔ IsMulCommutative D.VH) ∧
      (IsMulCommutative D.UH ↔ D.V ≤ D.QH) := by
  have hc : (D.H ⊓ centralizer (D.Vplus : Set G)) ⊓
      (D.H ⊓ normalizer (D.V : Set G)) = D.H ⊓ centralizer (D.V : Set G) := by
    apply le_antisymm
    · intro x hx
      have hxM : x ∈ M := hbound
        ⟨Subgroup.centralizer_le_normalizer _ (h.H_centralizes hx.1.1),
          Subgroup.centralizer_le_normalizer _ hx.1.2⟩
      exact ⟨hx.1.1, ((hcentral.le) ⟨hxM, hx.1.2⟩).2⟩
    · intro x hx
      exact ⟨⟨hx.1, Subgroup.centralizer_le h.plus_le hx.2⟩,
        hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  have he := h.lemma_F_9_4_three hc
  have hu : IsMulCommutative D.UH ↔ IsElementaryAbelian 2 D.UH := by
    constructor
    · intro hU
      let : IsMulCommutative (conjugateSpanBy D.Vplus D.H) := hU
      let := h.elementary
      let : IsElementaryAbelian 2 D.Vplus := IsElementaryAbelian.of_le h.plus_le
      exact conjugateSpanBy_elementary_of_commutative D.Vplus D.H
    · intro hU
      exact hU.toIsMulCommutative
  have hv : IsMulCommutative D.VH ↔ IsElementaryAbelian 2 D.VH := by
    constructor
    · intro hV
      let : IsMulCommutative (conjugateSpanBy D.V D.H) := hV
      let := h.elementary
      exact conjugateSpanBy_elementary_of_commutative D.V D.H
    · intro hV
      exact hV.toIsMulCommutative
  exact ⟨hu.trans (he.2.trans hv.symm), hu.trans he.1.symm⟩

end CFSG.Quasithin.Chapter13.Section05
end
