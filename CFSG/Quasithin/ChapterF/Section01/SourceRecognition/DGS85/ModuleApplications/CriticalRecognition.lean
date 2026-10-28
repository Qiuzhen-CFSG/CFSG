module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalActorBounds
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalDefinition

/-!
# Full corrected quadratic recognition on the original DGS critical quotient

The actor is the image of the original B through L → L/O₂(L) → D.
The vector quotient is Z/(Z∩Z(L)), identified through the original
conjugation action with the quotient by its global fixed space. Quadraticity
and the corrected Sylow-fixed generation descend along that exact vector
projection. The complete binary Chapter 5 catalogue gives the size bound;
a strict comparison produces an actual marked SL₂ natural module with all
p.113 consequences. Both unitary degree-one cases and Sz(2) are included.

A second application starts from the source natural-module definition on
the same quotient, as supplied by (6.3), and proves the consequences without
additional generation or residual-fixed-space assumptions.

Source: DGS85, *Groups and Graphs*, (5.12), pp.113–115, applied in (7.1),
pp.126–127, and (9.3). The graph owners retain construction of Z and the
local model map, actor placement, faithfulness, original generation, residual
fixed space and the comparisons. Identifying Z∩Z(L) with Ω₁(Z(L)) when the
source needs that equality also remains with those owners.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
universe u
variable {L D : Type u} [Group L] [Finite L] [Group D] [Finite D]

/-- Corrected DGS (5.12) applied as in (7.1) and (9.3): the vectors are
Z/(Z∩Z(L)), and the actor is the original B's image through L/O₂(L).
Generation on this very quotient is proved from generation on Z. -/
theorem critical_rank_one_bound_and_recognition
    (M : BinaryRankOneModel D)
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* D)
    (ρ : Representation (ZMod 2) D (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 D) (B : Subgroup L)
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (hres : fixedSpace (globalFixedQuotient ρ) (pResidual 2 D) = ⊥) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    GeneratedByFixedSpace (globalFixedQuotient ρ) S ∧
    Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ≤
      Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸ fixedSpace (globalFixedQuotient ρ)
        (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∧
    (Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸ fixedSpace (globalFixedQuotient ρ)
        (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) <
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ^ 2 →
      NaturalRealization (globalFixedQuotient ρ) S) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  have hq := quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (globalFixedQuotient_mk ρ g v).symm) _ hquad
  have hg := globalFixedQuotient_generated Z ρ S hgen
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,hg,
    binary_rank_one_bound_and_recognition M (globalFixedQuotient ρ) hf S _ hBS hq hg hres⟩

open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- When an earlier source theorem already supplies the p.112 natural
module on the original quotient, its p.113 consequences need no new
generation or residual fixed-space assumptions. -/
theorem critical_sourceNatural_consequences
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 SL(2,F)) (hf : Function.Injective (globalFixedQuotient ρ))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hnat : IsSourceNatural (globalFixedQuotient ρ) S n) :
    let σ := globalFixedQuotient ρ
    centralPart Z = fixedSpace ρ ⊤ ∧
    σ.IsIrreducible ∧ Nat.card (fixedSpace σ S)=2^n ∧
    (∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 → fixedSpace σ (zpowers t)=fixedSpace σ S) ∧
    (∀ g ∉ normalizer (S : Set SL(2,F)),
      IsCompl (fixedSpace σ S) (fixedSpace σ (g • S : Sylow 2 SL(2,F)))) ∧
    (∀ v w : Additive Z ⧸ fixedSpace ρ ⊤, v ≠ 0 → w ≠ 0 → ∃ g, σ g v=w) ∧
    ∃ E : (Additive Z ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (σ g v)=Matrix.mulVec g.val (E v) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    sourceNatural_coordinates_and_consequences (globalFixedQuotient ρ) hf S hn hF hnat⟩
end CFSG.Quasithin.DGS85.ModuleApplications
