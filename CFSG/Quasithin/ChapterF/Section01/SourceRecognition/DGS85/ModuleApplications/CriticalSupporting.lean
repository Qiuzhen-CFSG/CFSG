module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalRecognition
public import Theory.Representation.RankOne.QuadraticRecognition.SylowPlacement
public import Theory.Representation.RankOne.QuadraticRecognition.ElementFixedSpaces
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiOddFixedSpaces

/-!
# Supporting quadratic-module results on the original critical quotient

The vectors remain Z/(Z∩Z(L)), identified with the global-fixed quotient
through the original conjugation action. The actors remain images through
L → L/O₂(L) and the specified model isomorphism. Quadraticity descends
along the original vector projection, giving the actual Sylow omega-center
placement. The individual SL₂ and Suzuki estimates retain the defining
field parameter; the displacement equality uses the same quotient operator.
Complementary SL₂ or Suzuki omega fixed spaces also give the odd-element conclusion.

Source: DGS85, *Groups and Graphs*, (5.8)–(5.11), pp.109–112, on the
critical module of (7.1), pp.126–127. The placement and individual estimates
are the module inputs used in (8.2), (8.3), (8.6) and (8.7), pp.134–141.
The graph owners retain construction and identification of each original
module, its local marking, faithfulness, actor placement and complements.
The corrected generation premise required by (5.12) and its descent are
retained separately in CriticalRecognition; these estimates do not need it.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
universe u
variable {L D : Type u} [Group L] [Finite L] [Group D] [Finite D]

omit [Finite L] in
/-- DGS (5.9) on the original critical actor: the image of B through the
actual L/O₂(L) marking lies in Ω₁(Z(S)). Quadraticity descends through the
literal quotient Z/(Z∩Z(L)). -/
theorem critical_quadratic_actor_le_omega_center
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
    (hf : Function.Injective (globalFixedQuotient ρ)) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤
      omegaOneAmbient ((center S).map (S : Subgroup D).subtype) := by
  have hq := quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (globalFixedQuotient_mk ρ g v).symm) _ hquad
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    quadratic_actor_le_omega_center M (globalFixedQuotient ρ) hf S _ hBS hq⟩

variable {F : Type u} [Field F] [Finite F] [CharP F 2]

/-- DGS (5.10)(a) on a nontrivial original actor in the critical quotient.
The lower bound uses the defining field of the same L/O₂(L) model. -/
theorem critical_sl2_element_fixed_index
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 SL(2,F)) (t : L)
    (ht : e (QuotientGroup.mk' (pCore 2 L) t) ∈ S)
    (ht1 : e (QuotientGroup.mk' (pCore 2 L) t) ≠ 1)
    (hf : Function.Injective (globalFixedQuotient ρ))
    {n : ℕ} (hF : Nat.card F=2^n) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    2^n ≤ Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
      fixedSpace (globalFixedQuotient ρ) (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))) ∧
    Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
      fixedSpace (globalFixedQuotient ρ) (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))) =
      Nat.card (LinearMap.range
        (globalFixedQuotient ρ (e (QuotientGroup.mk' (pCore 2 L) t)) - LinearMap.id)) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    sl2_element_fixed_index (globalFixedQuotient ρ) hf S ht ht1 hF,
    card_fixed_quotient_eq_displacement (globalFixedQuotient ρ) _⟩

/-- The source (5.11) odd-element conclusion on the same critical quotient.
The graph owner retains construction of the complementary Sylow fixed
spaces; no recognition or natural-module output is assumed. -/
theorem critical_sl2_odd_fixed_eq_bot
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S T : Sylow 2 SL(2,F))
    (hc : IsCompl (fixedSpace (globalFixedQuotient ρ) S)
      (fixedSpace (globalFixedQuotient ρ) T))
    (a : L) (ho : Odd (orderOf a))
    (ha1 : e (QuotientGroup.mk' (pCore 2 L) a) ≠ 1) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    fixedSpace (globalFixedQuotient ρ)
      (zpowers (e (QuotientGroup.mk' (pCore 2 L) a))) = ⊥ := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    sl2_odd_fixed_eq_bot_of_complement (globalFixedQuotient ρ) S T hc _ ho ?_ ha1⟩
  rw [←map_pow,←map_pow,pow_orderOf_eq_one,map_one,map_one]
omit [Field F] [Finite F] [CharP F 2] in
/-- The Suzuki clause of (5.10)(b) on the literal original critical quotient.
The actor is the image of the specified t, and m=0 is included. -/
theorem critical_suzuki_element_fixed_index
    (m : ℕ) (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (t : L) (ht : orderOf (e (QuotientGroup.mk' (pCore 2 L) t)) = 2)
    (hf : Function.Injective (globalFixedQuotient ρ)) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    2^(2*(2*m+1)) ≤ Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
      fixedSpace (globalFixedQuotient ρ) (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    suzuki_element_fixed_index m (globalFixedQuotient ρ) hf _ ht⟩

omit [Finite L] in
/-- The Suzuki (5.11) conclusion at every parameter on the original critical
quotient. The graph owner supplies the complementary omega fixed spaces. -/
theorem critical_suzuki_odd_fixed_eq_bot
    (m : ℕ) (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S T : Sylow 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) (hST : S≠T)
    (hc : IsCompl
      (fixedSpace (globalFixedQuotient ρ) (omegaOneAmbient (S : Subgroup _)))
      (fixedSpace (globalFixedQuotient ρ) (omegaOneAmbient (T : Subgroup _))))
    (a : L) (ho : Odd (orderOf a))
    (ha1 : e (QuotientGroup.mk' (pCore 2 L) a) ≠ 1) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    fixedSpace (globalFixedQuotient ρ)
      (zpowers (e (QuotientGroup.mk' (pCore 2 L) a))) = ⊥ := by
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    suzuki_all_odd_fixed_eq_bot_of_complement m (globalFixedQuotient ρ) S T hST hc _ ?_ ha1⟩
  apply Odd.of_dvd_nat ho
  apply orderOf_dvd_of_pow_eq_one
  rw [←map_pow,←map_pow,pow_orderOf_eq_one,map_one,map_one]

end CFSG.Quasithin.DGS85.ModuleApplications
