module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalActorBounds
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiAllActors

/-!
# Excluding every Suzuki row on the original DGS critical quotient

Apply the uniform Suzuki square bound, including Sz(2), to Z/(Z∩Z(L)).
The actor is the image of the original B under L → L/O₂(L) → Sz(q).
Quadraticity and the corrected fixed-space generation descend along the
literal vector quotient. Thus the strict inequality in DGS (7.1) or (9.3)
excludes all Suzuki parameters on this same quotient. The graph owners
retain construction of Z, the original model map, actor placement, faithful
quotient action, original generation and the strict inequality.
Source: DGS85, printed pp.113–114,126–127.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
variable {L : Type*} [Group L] [Finite L]

/-- The Suzuki square bound on the same critical quotient and original image actor.
It contradicts the strict inequality used in DGS (7.1) and (9.3). -/
theorem critical_suzuki_all_square_bound
    (m : ℕ)
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (B : Subgroup L)
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (globalFixedQuotient ρ)) :
    centralPart Z = fixedSpace ρ ⊤ ∧
      GeneratedByFixedSpace (globalFixedQuotient ρ) S ∧
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ^ 2 ≤
        Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
          fixedSpace (globalFixedQuotient ρ)
            (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  have hq := quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (globalFixedQuotient_mk ρ g v).symm) _ hquad
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    globalFixedQuotient_generated Z ρ S hgen,
    suzuki_all_square_bound m (globalFixedQuotient ρ) hf S _ hBS hq⟩

end CFSG.Quasithin.DGS85.ModuleApplications
