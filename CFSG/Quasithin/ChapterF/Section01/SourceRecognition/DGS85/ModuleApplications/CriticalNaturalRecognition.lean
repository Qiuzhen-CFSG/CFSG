module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalActorBounds
public import Theory.Representation.RankOne.QuadraticRecognition.SL2ProperActor

/-!
# Natural recognition on the original DGS critical quotient

For an arbitrary actor B in the original local group L, retain the precise map
L → L/O₂(L) → SL₂(F), its image of B, and the vector quotient Z/(Z∩Z(L)).
The corrected fixed-space generation hypothesis descends from Z along the
actual quotient map. Under quadraticity, residual fixed-space vanishing, and
the strict source inequality, recognition gives the source natural module,
its prime-field irreducibility, all Sylow fixed orders and complementary
fixed spaces, and transitivity on nonzero vectors. Equivariant coordinates
retain the original defining field and matrix action.

This is the SL₂ application of DGS85 (5.12) in (7.1), printed pp.126–127,
and (9.3). The graph owners supply the original Z, model map, actor placement,
faithfulness, generation, residual fixed-space and strict-inequality premises.
The identification of Z∩Z(L) with the source Ω₁(Z(L)) also remains theirs.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
variable {L F : Type*} [Group L] [Finite L]
  [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The strict actor recognition and the exact p.113 consequences on the
same original central quotient, including proper actors and field order two. -/
theorem critical_sl2_strict_actor_natural
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 SL(2,F)) (B : Subgroup L)
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (hres : fixedSpace (globalFixedQuotient ρ) (pResidual 2 SL(2,F)) = ⊥)
    {n : ℕ} (hF : Nat.card F = 2^n)
    (hstrict : Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
      fixedSpace (globalFixedQuotient ρ)
        (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) <
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ^ 2) :
    let σ := globalFixedQuotient ρ
    centralPart Z = fixedSpace ρ ⊤ ∧
    IsSourceNatural σ S n ∧ σ.IsIrreducible ∧
    Nat.card (fixedSpace σ S) = Nat.card F ∧
    (∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 →
      fixedSpace σ (zpowers t) = fixedSpace σ S) ∧
    (∀ g ∉ normalizer (S : Set SL(2,F)),
      IsCompl (fixedSpace σ S) (fixedSpace σ (g • S : Sylow 2 SL(2,F)))) ∧
    (∀ v w : Additive Z ⧸ fixedSpace ρ ⊤, v ≠ 0 → w ≠ 0 → ∃ g, σ g v = w) ∧
    ∃ E : (Additive Z ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (σ g v) = Matrix.mulVec g.val (E v) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  have hfix : fixedSpace (globalFixedQuotient ρ) ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone (globalFixedQuotient ρ) le_top).trans hres.le)
  have hq := quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (globalFixedQuotient_mk ρ g v).symm) _ hquad
  have hg := globalFixedQuotient_generated Z ρ S hgen
  obtain ⟨hnat,E,he⟩ := sl2_strict_actor_natural (globalFixedQuotient ρ)
    hf S _ hBS hq hg hfix hF hstrict
  obtain ⟨hc,hu⟩ := sl2_natural_fixed_spaces (globalFixedQuotient ρ) S hnat.2.2 hg hfix E
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact,hnat,
    irreducible_of_natural_coordinates _ E he,hc,hu,?_,?_,E,he⟩
  · intro g hgn
    exact sl2_sylow_fixed_isCompl _ S (g • S)
      (fun h => hgn (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)) hnat.2.2 hg hfix
  · intro v w hv hw
    exact transitive_of_natural_coordinates _ E he hv hw

end CFSG.Quasithin.DGS85.ModuleApplications
