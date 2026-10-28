module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalSupporting
public import Theory.Representation.RankOne.QuadraticRecognition.QuadraticPairs

/-!
# Quadratic-pair fixed spaces on the original critical quotient

The vector quotient remains Z/(Z∩Z(L)), through its proved identification
with the global-fixed quotient of the original conjugation action. Both
actors and the conjugator retain their images under L → L/O₂(L) and the
specified rank-one model isomorphism. Quadraticity and generation by the
translates of C_Z(B) descend along the literal vector projection.

Perfectness is proved for SL₂ over fields of size at least four and for
Sz(2^(2m+1)), m>0. The perfect-group quadratic-pair theorem then gives
the fixed-space equality. The pair-generation equation remains an explicit
premise: its general rank-one discharge remains with the quadratic-module
family, so these conditional applications do not assert full (5.10)(c).

Source: DGS85, *Groups and Graphs*, (5.8)(d) and (5.10)(c), printed
pp.109–111; the critical quotient is from (7.1), printed pp.126–127.
The graph owners retain construction of their original modules, conjugation
markings, quadratic actors and vector-generation premises.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
universe u v
variable {L : Type u} {D : Type v} [Group L] [Group D]

private theorem critical_fixedSpace_eq_of_perfect_pair [Group.IsPerfect D]
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* D)
    (ρ : Representation (ZMod 2) D (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (B : Subgroup L) (t g : L) (ht : t∈B)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hspan : GeneratedByFixedSpace ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hpair : zpowers (e (QuotientGroup.mk' (pCore 2 L) t)) ⊔
      (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).map
        (MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) g))).toMonoidHom = ⊤) :
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
    fixedSpace_eq_of_perfect_quadratic_pair (globalFixedQuotient ρ) A _ _
      (mem_map_of_mem _ ht) hq
      (SL2SylowFixedRecognition.quadratic_conjugate (globalFixedQuotient ρ) hq _)
      hpair hsp⟩

variable {F : Type v} [Field F] [Finite F]

/-- DGS (5.10)(c) for the actual SL₂ critical quotient once its specified
pair generates the model. Perfectness and quotient fixed-space generation
are discharged here; the pair-generation equation remains explicit. -/
theorem critical_sl2_fixedSpace_eq_of_pair_generation
    (hF : 4 ≤ Nat.card F)
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (B : Subgroup L) (t g : L) (ht : t∈B)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hspan : GeneratedByFixedSpace ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hpair : zpowers (e (QuotientGroup.mk' (pCore 2 L) t)) ⊔
      (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).map
        (MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) g))).toMonoidHom = ⊤) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    fixedSpace (globalFixedQuotient ρ)
      (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) =
    fixedSpace (globalFixedQuotient ρ) (zpowers (e (QuotientGroup.mk' (pCore 2 L) t))) := by
  let : Group.IsPerfect SL(2,F) := SL2SylowFixedRecognition.perfect hF
  exact critical_fixedSpace_eq_of_perfect_pair Z e ρ hact B t g ht hquad hspan hpair

/-- The corresponding Suzuki critical-quotient equality. The supplied
source pair and vector generation are kept at their original markings. -/
theorem critical_suzuki_fixedSpace_eq_of_pair_generation
    {m : ℕ} (hm : 0<m)
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (B : Subgroup L) (t g : L) (ht : t∈B)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hspan : GeneratedByFixedSpace ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hpair : zpowers (e (QuotientGroup.mk' (pCore 2 L) t)) ⊔
      (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).map
        (MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) g))).toMonoidHom = ⊤) :
    centralPart Z = fixedSpace ρ ⊤ ∧
    fixedSpace (globalFixedQuotient ρ)
      (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) =
    fixedSpace (globalFixedQuotient ρ) (zpowers (e (QuotientGroup.mk' (pCore 2 L) t))) := by
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsPerfect (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
    constructor
    rcases (inferInstance : (commutator (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top
      with h|h
    · exact False.elim (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
        ⟨⟨1,(derivedSeries_one _).trans h⟩⟩)
    · exact h
  exact critical_fixedSpace_eq_of_perfect_pair Z e ρ hact B t g ht hquad hspan hpair
end CFSG.Quasithin.DGS85.ModuleApplications
