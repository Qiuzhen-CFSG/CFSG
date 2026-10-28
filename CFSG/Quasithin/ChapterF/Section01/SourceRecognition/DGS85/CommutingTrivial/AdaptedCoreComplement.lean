module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CoreElementaryQuotient
public import Theory.Representation.BinaryConjugationSection.InvariantComplement

/-!
# The original adapted natural subgroup

A complement to the specified image of V in the canonical Q/Z module
pulls back to the subgroup W used after 9.10(6). Its natural conjugation
coordinates agree with the canonical quotient coordinates; W∩V=Z and
W∨V=Q. The original center order gives |W|=q³, and W escapes the adjacent
core because Q does while V is contained in it.

Source: DGS, *Groups and Graphs* (1985), printed p.150, first paragraph.
The invariant complement remains the explicit output needed from the
independent natural self-extension splitting argument.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]

/-- The adapted subgroup in the first paragraph of p.150, with its actual action. -/
theorem adapted_core_complement
    (Γ : Bool → Subgroup G) (beta x : Vertex Γ)
    {F Y : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) Y)
    (c : BinaryConjugationSection (graphLocalGroup Γ beta) (Q Γ beta) (Z Γ beta)
      (ρ.comp (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))))
    (hVQ : V Γ beta 1 ≤ Q Γ beta)
    (X K : Subrepresentation ρ) (hX : X.toSubmodule = c.imageSpace (V Γ beta 1))
    (hK : IsCompl X.toSubmodule K.toSubmodule)
    (eK : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      K.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → F))
    (heK : ∀ g k, eK (K.toRepresentation g k) = Matrix.mulVec g.val (eK k))
    (hZcard : Nat.card (Z Γ beta) = Nat.card F)
    (hVx : V Γ beta 1 ≤ Q Γ x) (hQx : ¬ Q Γ beta ≤ Q Γ x) :
    let π := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta)))
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    ∃ (W : Subgroup G) (hWQ : W ≤ Q Γ beta),
      W ⊓ V Γ beta 1 = Z Γ beta ∧ W ⊔ V Γ beta 1 = Q Γ beta ∧
      Nat.card W = Nat.card F ^ 3 ∧ ¬ W ≤ Q Γ x ∧
      ∃ cW : BinaryConjugationSection (graphLocalGroup Γ beta) W (Z Γ beta)
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π),
        ∀ w : W, (eK.symm (cW.coordinates w).toAdd : Y) =
          (c.coordinates (inclusion hWQ w)).toAdd := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨W,hWQ,hWV,hWsup,cW,he⟩ := BinaryConjugationSection.exists_complementary_section
    (graphLocalGroup Γ beta) (Q Γ beta) (V Γ beta 1) (Z Γ beta) hVQ (Z_le_V Γ beta 1)
    (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))
    ρ ((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)) c X K hX hK eK heK
  refine ⟨W,hWQ,hWV,hWsup,?_,?_,cW,he⟩
  · rw [cW.card_section,hZcard,Nat.card_fun,Nat.card_fin]
    ring
  · intro hW
    exact hQx (hWsup ▸ sup_le hW hVx)
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
