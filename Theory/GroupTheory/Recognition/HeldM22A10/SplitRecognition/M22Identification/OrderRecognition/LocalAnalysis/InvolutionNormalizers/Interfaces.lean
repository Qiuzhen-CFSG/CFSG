module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Elementary

/-!
# The automizer conclusions in Janko's involution argument

These intermediate conclusions separate the ambient fusion and automizer
arguments from Gaschütz's splitting theorem. The quotients are by the actual
elementary subgroups inside their ambient normalizers. The fusion witnesses
belong to those same normalizers. No inhabitants of these structures are
assumed or constructed here.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemmas 2 and 6, pp.5–7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

/-- The quotient and orbit conclusions of Lemma 2, to be proved under fusion of
the marked involution with the actor `d`. -/
public structure FNormalizerAction {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : Prop where
  quotient : Nonempty
    ((normalizer (CaseII.F D k : Set G) ⧸
      (CaseII.F D k).subgroupOf (normalizer (CaseII.F D k : Set G))) ≃*
        Equiv.Perm (Fin 5))
  fusion : ∀ x y : CaseII.F D k, x ≠ 1 → y ≠ 1 →
    ∃ g : normalizer (CaseII.F D k : Set G), (g : G) * x * (g : G)⁻¹ = y

/-- The quotient and orbit conclusions of Lemma 6. Gaschütz's theorem and the
local complement then give the required complement isomorphic to A6. -/
public structure ENormalizerAction {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : Prop where
  quotient : Nonempty
    ((normalizer (CaseII.E D k : Set G) ⧸
      (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))) ≃*
        alternatingGroup (Fin 6))
  fusion : ∀ x y : CaseII.E D k, x ≠ 1 → y ≠ 1 →
    ∃ g : normalizer (CaseII.E D k : Set G), (g : G) * x * (g : G)⁻¹ = y

end Theory.GroupTheory.HeldM22A10.M22Identification
