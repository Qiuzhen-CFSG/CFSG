module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalCentralQuotient
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Strict
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiActors

/-!
# Size bounds on the original DGS critical central quotient

Let Z be the original elementary abelian normal subgroup of L. The model map
is exactly L → L/O₂(L) → D, and the actor is the image of the specified original
subgroup B under that same map. The vector denominator is Z ∩ Z(L), identified
with the fixed space using the original conjugation equation. Fixed-space
generation descends from Z to this literal quotient.

The SL₂ estimate now accepts every subgroup of the prescribed Sylow. The
nondegenerate Suzuki estimate is the square bound, so the strict inequality
in DGS85 (7.1), pp.126–127, or (9.3) cannot hold on this quotient in a Suzuki
row. These are conditional graph applications: the graph owners construct Z,
the model marking and actor placement, and prove quotient faithfulness,
quadraticity, generation and the relevant strict comparison. They also retain
the source identification of Z ∩ Z(L) with Ω₁(Z(L)). No Sz(2) or unitary
recognition is inferred from these estimates.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
variable {L D : Type*} [Group L] [Group D]

/-- The denominator is the actual central part for any marked local model. -/
theorem centralPart_eq_fixedSpace_model
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* D)
    (ρ : Representation (ZMod 2) D (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹) :
    centralPart Z = fixedSpace ρ ⊤ := by
  ext v
  change (v.toMul : L) ∈ Subgroup.center L ↔ v ∈ fixedSpace ρ ⊤
  constructor
  · intro hv g
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g.val
    change e (QuotientGroup.mk' (pCore 2 L) l) = g.val at hl
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ g.val v).toMul : L) = (v.toMul : L)
    rw [←hl,hact,Subgroup.mem_center_iff.mp hv l,mul_inv_cancel_right]
  · intro hv
    apply Subgroup.mem_center_iff.mpr
    intro l
    have hh := congrArg (fun w : Additive Z => (w.toMul : L))
      (hv ⟨e (QuotientGroup.mk' (pCore 2 L) l),mem_top _⟩)
    change ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) = _ at hh
    rw [hact] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- The correction in (5.12) descends from the original module, on the same actor. -/
theorem globalFixedQuotient_generated
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (ρ : Representation (ZMod 2) D (Additive Z)) (S : Subgroup D)
    (hgen : GeneratedByFixedSpace ρ S) :
    GeneratedByFixedSpace (globalFixedQuotient ρ) S :=
  generatedByFixedSpace_quotient ρ (globalFixedSubrepresentation ρ) S hgen

variable [Finite L]

/-- The SL₂ bound for the exact image of B on Z/(Z ∩ Z(L)). -/
theorem critical_sl2_actor_bound
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 SL(2,F)) (B : Subgroup L)
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (globalFixedQuotient ρ))
    {n : ℕ} (hF : Nat.card F = 2^n) :
    centralPart Z = fixedSpace ρ ⊤ ∧
      GeneratedByFixedSpace (globalFixedQuotient ρ) S ∧
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ≤
        Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
          fixedSpace (globalFixedQuotient ρ)
            (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    globalFixedQuotient_generated Z ρ S hgen,
    sl2_actor_bound (globalFixedQuotient ρ) hf S _ hBS hF⟩

/-- The strict SL₂ branch makes the same critical central quotient irreducible,
without requiring its actor to be the full Sylow. -/
theorem critical_sl2_strict_actor_irreducible
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 SL(2,F)) (B : Subgroup L)
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ≤ S)
    (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (globalFixedQuotient ρ))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hstrict : Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
      fixedSpace (globalFixedQuotient ρ)
        (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) <
      Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) ^ 2) :
    centralPart Z = fixedSpace ρ ⊤ ∧ (globalFixedQuotient ρ).IsIrreducible := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ n)
  have hfix : fixedSpace (globalFixedQuotient ρ) ⊤ = ⊥ :=
    SL2SylowFixedRecognition.centralQuotient_fixed_eq_bot ρ hlarge
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    sl2_strict_actor_irreducible (globalFixedQuotient ρ) hf S _ hBS
      (globalFixedQuotient_generated Z ρ S hgen) hfix hn hF hstrict⟩

/-- The Suzuki square bound on the same critical quotient and original image actor.
It contradicts the strict inequality used in DGS (7.1) and (9.3). -/
theorem critical_suzuki_square_bound
    {m : ℕ} (hm : 0 < m)
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
    suzuki_square_bound hm (globalFixedQuotient ρ) hf S _ hBS hq⟩

end CFSG.Quasithin.DGS85.ModuleApplications
