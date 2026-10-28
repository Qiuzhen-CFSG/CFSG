module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalPairs
public import Theory.Representation.RankOne.QuadraticRecognition.SL2PairGeneration
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiPairGeneration

/-!
# DGS fixed-space equality on the literal critical quotient

The actor is the image of the original subgroup B under
L → L/O₂(L) and the specified model isomorphism. The vector quotient is
Z/(Z∩Z(L)), identified with the global-fixed quotient of the original
conjugation representation. Quadraticity and generation by translates of
C_Z(B) descend along the actual vector projection.

The defining-field pair-generation theorems discharge the extra equation in
CriticalPairs. These are the complete binary linear and Suzuki clauses of
DGS85 (5.10)(c), printed pp.110–111, on the quotient from (7.1), pp.126–127,
used in the fixed-space comparisons of Chapter 8. The graph owners retain
construction of the module, original actor and conjugation marking, and
proof of the literal actor-fixed generation premise.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
universe u v
variable {L : Type u} [Group L]

/-- The linear critical quotient satisfies source (5.10)(c), with pair
generation proved and the original actor-fixed generation descended here. -/
theorem critical_sl2_quadratic_fixedSpace_eq
    {F : Type v} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0<n) (hF : Nat.card F=2^n)
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 SL(2,F)) (B : Subgroup L) (t : L) (ht : t∈B)
    (ht1 : e (QuotientGroup.mk' (pCore 2 L) t) ≠ 1)
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hBc : 4≤Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hspan : GeneratedByFixedSpace ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    fixedSpace (globalFixedQuotient ρ)
      (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) =
    fixedSpace (globalFixedQuotient ρ) (zpowers (e (QuotientGroup.mk' (pCore 2 L) t))) := by
  let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hq : IsQuadratic (globalFixedQuotient ρ) A :=
    quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
      (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
      (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  have hsp : GeneratedByFixedSpace (globalFixedQuotient ρ) A :=
    generatedByFixedSpace_quotient ρ (globalFixedSubrepresentation ρ) A hspan
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    sl2_quadratic_fixedSpace_eq (globalFixedQuotient ρ) hn hF S A hBS hBc hq hsp
      _ (mem_map_of_mem _ ht) ht1⟩

/-- The complete Suzuki critical-quotient clause, retaining faithfulness of
the actual quotient action and covering every source Suzuki parameter. -/
theorem critical_suzuki_quadratic_fixedSpace_eq
    (m : ℕ) (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (B : Subgroup L) (t : L) (ht : t∈B)
    (ht1 : e (QuotientGroup.mk' (pCore 2 L) t) ≠ 1)
    (hBc : 4≤Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hspan : GeneratedByFixedSpace ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    fixedSpace (globalFixedQuotient ρ)
      (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) =
    fixedSpace (globalFixedQuotient ρ) (zpowers (e (QuotientGroup.mk' (pCore 2 L) t))) := by
  let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hq : IsQuadratic (globalFixedQuotient ρ) A :=
    quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
      (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
      (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  have hsp : GeneratedByFixedSpace (globalFixedQuotient ρ) A :=
    generatedByFixedSpace_quotient ρ (globalFixedSubrepresentation ρ) A hspan
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    suzuki_quadratic_fixedSpace_eq m (globalFixedQuotient ρ) hf A hBc hq hsp
      _ (mem_map_of_mem _ ht) ht1⟩
end CFSG.Quasithin.DGS85.ModuleApplications
