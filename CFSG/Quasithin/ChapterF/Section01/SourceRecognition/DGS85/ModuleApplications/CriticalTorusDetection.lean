module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalFixedGenerated
public import Theory.Representation.RankOne.QuadraticRecognition.TorusFixedSpace

/-!
# Norm-one torus detection on the literal DGS critical quotient

The original element l maps through L → L/O₂(L) to the specified norm-one
torus matrix. The original actor B follows the same map. Quadraticity
descends from Z to Z/(Z∩Z(L)), and its actor fixed space generates the local
fixed-field SL₂ block by construction. A faithful quotient action detects
every nontrivial torus image on that local block.

This supplies the faithful whole-block centralization exclusion in DGS85
(5.10)(b), p.112, for the exact critical quotient used in Chapter 8.
The original group action, quotient faithfulness and normalized root placement
remain graph inputs, owned by the critical-module and source assembly tasks.
The fixed-point-free conclusion on the local central quotient is not asserted.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
variable {L F : Type*} [Group L] [Field F] [Finite F] [CharP F 2]

/-- The original torus element moves the constructed local block on the
same critical quotient, retaining its exact unitary image. -/
theorem critical_su3_normOne_moves_fixedGenerated
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0<n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* J.specialSubgroup)
    (ρ : Representation (ZMod 2) J.specialSubgroup (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (B : Subgroup L)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ central J hJ)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (k : normOne J) (l : L)
    (hl : e (QuotientGroup.mk' (pCore 2 L) l) = hermitianTorusSU J hJ k.val)
    (hl1 : e (QuotientGroup.mk' (pCore 2 L) l) ≠ 1) :
    centralPart Z = fixedSpace ρ ⊤ ∧
      let σ := globalFixedQuotient ρ
      let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      let j := block J hJ
      let W := fixedGeneratedSubrepresentation (σ.comp j) (A.comap j)
      GeneratedByFixedSpace W.toRepresentation (A.comap j) ∧
      ∃ v ∈ W.toSubmodule, σ (e (QuotientGroup.mk' (pCore 2 L) l)) v ≠ v := by
  let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hq : IsQuadratic (globalFixedQuotient ρ) A :=
    quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
      (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
      (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact, fixedGenerated_generated _ _, ?_⟩
  simpa only [hl] using su3_normOne_moves_fixedGenerated J hJ hn hcard hconj
    (globalFixedQuotient ρ) hf A hB hq k (by rwa [←hl])

/-- The original torus element moves the constructed local block on the
same critical quotient, retaining its exact unitary image. -/
theorem critical_psu3_normOne_moves_fixedGenerated
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0<n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* (ProjectiveSpecialUnitaryMatrixGroup J))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (B : Subgroup L)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ centralImage J hJ)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (k : normOne J) (l : L)
    (hl : e (QuotientGroup.mk' (pCore 2 L) l) = normOneMap J hJ k)
    (hl1 : e (QuotientGroup.mk' (pCore 2 L) l) ≠ 1) :
    centralPart Z = fixedSpace ρ ⊤ ∧
      let σ := globalFixedQuotient ρ
      let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      let j := J.specialToProjective.comp (block J hJ)
      let W := fixedGeneratedSubrepresentation (σ.comp j) (A.comap j)
      GeneratedByFixedSpace W.toRepresentation (A.comap j) ∧
      ∃ v ∈ W.toSubmodule, σ (e (QuotientGroup.mk' (pCore 2 L) l)) v ≠ v := by
  let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hq : IsQuadratic (globalFixedQuotient ρ) A :=
    quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
      (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
      (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact, fixedGenerated_generated _ _, ?_⟩
  simpa only [hl] using psu3_normOne_moves_fixedGenerated J hJ hn hcard hconj
    (globalFixedQuotient ρ) hf A hB hq k (by rwa [←hl])

end CFSG.Quasithin.DGS85.ModuleApplications
