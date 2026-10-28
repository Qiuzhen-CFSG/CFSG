module

public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.AbelianConjugateSpan
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Central elementary sections of conjugate spans

Let a normal subgroup Q lie in P C(B), where B is elementary abelian and
B ≤ P ≤ Q. If [P,P] lies in a normal subgroup Z, then [⟨Bᴳ⟩,Q] ≤ Z and
the image of ⟨Bᴳ⟩ modulo Z is elementary abelian. In the quotient, Q
centralizes B and therefore its entire conjugate span; that span lies in Q.

This elementary propagation argument constructs the section used in
Aschbacher--Smith, E.2.17, printed p.229, without further pair choices.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem conjugateSpan_central_section_of_centralizing_supplement
    (Q P B Z : Subgroup G) [Q.Normal] [Z.Normal] [IsElementaryAbelian 2 B]
    (hP : P ≤ Q) (hB : B ≤ P) (hQ : Q ≤ P ⊔ centralizer (B : Set G))
    (hcomm : ⁅P,P⁆ ≤ Z) :
    ⁅conjugateSpanBy B ⊤,Q⁆ ≤ Z ∧
      IsElementaryAbelian 2 ((conjugateSpanBy B ⊤).map (QuotientGroup.mk' Z)) := by
  let π := QuotientGroup.mk' Z
  have hPcomm : ⁅P.map π,P.map π⁆ = ⊥ := by
    rw [←map_commutator,map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hcomm
  have hQC : Q.map π ≤ centralizer (B.map π : Set (G ⧸ Z)) := by
    apply le_trans (map_mono hQ)
    rw [map_sup]
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp hPcomm).trans (centralizer_le (map_mono hB))
    · exact map_centralizer_le_centralizer_image (B : Set G) π
  let : (Q.map π).Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  have hU : (conjugateSpanBy B ⊤).map π = conjugateSpanBy (B.map π) ⊤ := by
    rw [map_conjugateSpanBy,map_top_of_surjective π (QuotientGroup.mk'_surjective Z)]
  have hUC : Q.map π ≤ centralizer ((conjugateSpanBy B ⊤).map π : Set (G ⧸ Z)) := by
    rw [hU]
    exact le_centralizer_conjugateSpanBy_of_normalizes (Q.map π) (B.map π) ⊤
      le_normalizer_of_normal hQC
  have hUQ : conjugateSpanBy B ⊤ ≤ Q := conjugateSpanBy_le (hB.trans hP) le_normalizer_of_normal
  constructor
  · have hz : (⁅conjugateSpanBy B ⊤,Q⁆).map π = ⊥ := by
      rw [map_commutator,commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hUC
    simpa only [π,QuotientGroup.ker_mk'] using (map_eq_bot_iff _).mp hz
  · let : IsElementaryAbelian 2 (B.map π) := IsElementaryAbelian.map π
    have hc : IsMulCommutative ((conjugateSpanBy B ⊤).map π) :=
      le_centralizer_iff_isMulCommutative.mp ((map_mono hUQ).trans hUC)
    rw [hU] at hc ⊢
    exact conjugateSpanBy_elementary_of_commutative (B.map π) ⊤
end Subgroup
