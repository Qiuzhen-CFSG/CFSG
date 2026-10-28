module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalActorBounds
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryActors

/-!
# Excluding the nondegenerate unitary rows on the DGS critical quotient

For both SU₃(2ⁿ) and PSU₃(2ⁿ), n≥2, apply the square estimate to the original
central quotient Z/(Z∩Z(L)) and to the image of the original B under the exact
map L → L/O₂(L) → D. Keep the original Hermitian form and its field involution.
The source residual fixed-space premise implies zero global fixed space;
quadraticity and corrected generation descend along the actual vector map.
Thus the strict comparisons in DGS (7.1) and (9.3) exclude these unitary rows.
The graph owners supply Z, the local model equivalence, faithful quotient
representation, quadraticity, generation, residual fixed space and comparisons.
The small unitary cases over a field of order four remain separate.
Source: DGS85, *Groups and Graphs*, printed pp.113–114,126–127.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
variable {L F : Type*} [Group L] [Finite L] [Field F] [Finite F]

/-- The SU3 bounds on the same original central quotient and image actor. -/
theorem critical_su3_quadratic_bounds
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* J.specialSubgroup)
    (ρ : Representation (ZMod 2) J.specialSubgroup (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 J.specialSubgroup) (B : Subgroup L)
    (_hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (hres : fixedSpace (globalFixedQuotient ρ) (pResidual 2 J.specialSubgroup) = ⊥) :
    centralPart Z = fixedSpace ρ ⊤ ∧
      GeneratedByFixedSpace (globalFixedQuotient ρ) S ∧
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ≤
        Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
          fixedSpace (globalFixedQuotient ρ)
            (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∧
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ^ 2 ≤
        Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
          fixedSpace (globalFixedQuotient ρ)
            (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  have hq := quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (globalFixedQuotient_mk ρ g v).symm) _ hquad
  have hfix : fixedSpace (globalFixedQuotient ρ) ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone (globalFixedQuotient ρ) le_top).trans hres.le)
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    globalFixedQuotient_generated Z ρ S hgen,
    su3_quadratic_bounds J hn hcard hconj (globalFixedQuotient ρ) hf hfix _ hq⟩

/-- The PSU3 bounds on the same original central quotient and image actor. -/
theorem critical_psu3_quadratic_bounds
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* (ProjectiveSpecialUnitaryMatrixGroup J))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) (B : Subgroup L)
    (_hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (hres : fixedSpace (globalFixedQuotient ρ) (pResidual 2 (ProjectiveSpecialUnitaryMatrixGroup J)) = ⊥) :
    centralPart Z = fixedSpace ρ ⊤ ∧
      GeneratedByFixedSpace (globalFixedQuotient ρ) S ∧
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ≤
        Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
          fixedSpace (globalFixedQuotient ρ)
            (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∧
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ^ 2 ≤
        Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
          fixedSpace (globalFixedQuotient ρ)
            (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  have hq := quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (globalFixedQuotient_mk ρ g v).symm) _ hquad
  have hfix : fixedSpace (globalFixedQuotient ρ) ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone (globalFixedQuotient ρ) le_top).trans hres.le)
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    globalFixedQuotient_generated Z ρ S hgen,
    psu3_quadratic_bounds J hn hcard hconj (globalFixedQuotient ρ) hf hfix _ hq⟩

end CFSG.Quasithin.DGS85.ModuleApplications
