module
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalConsequences
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.PGroupCore

/-!+# The actual central quotient in the SL₂ branch of DGS (7.1)

Let Z be the original elementary abelian normal subgroup of the local group
L and mark L/O₂(L) by the actual matrix group SL₂(F). The input action must
agree with conjugation through this precise quotient map. Its global fixed
space is exactly Z ∩ Z(L). Generation by the original Sylow fixed vectors
descends along the literal quotient map; it is not an extra generation
assumption on the quotient.

The full-Sylow quadratic recognition theorem then supplies natural coordinates
on Z/(Z ∩ Z(L)), with the original conjugation formula. In DGS85 (7.1),
printed pp.126--127, the graph argument identifies Z ∩ Z(L) with Ω₁(Z(L)).
The graph owners retain that identification, the SL₂ actor marking, quadratic
action of the full Sylow, faithfulness of this central quotient, the strict
inequality and the original fixed-space generation premise. This conditional
SL₂ application does not establish the other rank-one alternatives of (5.12)
or the complete graph theorem.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.DGS85.ModuleApplications
variable {L F : Type*} [Group L] [Finite L]
  [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The literal vector subspace corresponding to Z ∩ Z(L). -/
def centralPart (Z : Subgroup L) [IsElementaryAbelian 2 Z] :
    Submodule (ZMod 2) (Additive Z) :=
  AddSubgroup.toZModSubmodule 2 ((Subgroup.center L).subgroupOf Z).toAddSubgroup

omit [Finite L] [Finite F] [CharP F 2] in
/-- The actor and vector quotient conventions agree with ambient conjugation. -/
theorem centralPart_eq_fixedSpace (Z : Subgroup L) [Z.Normal]
    [IsElementaryAbelian 2 Z] (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹) :
    centralPart Z = fixedSpace ρ ⊤ := by
  ext v
  change (v.toMul : L) ∈ Subgroup.center L ↔ v ∈ fixedSpace ρ ⊤
  constructor
  · intro hv g
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g.val
    simp only [Function.comp_apply] at hl
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ g.val v).toMul : L) = (v.toMul : L)
    rw [← hl,hact]
    rw [Subgroup.mem_center_iff.mp hv l,mul_inv_cancel_right]
  · intro hv
    apply Subgroup.mem_center_iff.mpr
    intro l
    have hh := congrArg (fun w : Additive Z => (w.toMul : L))
      (hv ⟨e (QuotientGroup.mk' (pCore 2 L) l),mem_top _⟩)
    change ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) = _ at hh
    rw [hact] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

omit [Finite L] [Finite F] [CharP F 2] in
/-- Fixed-space generation for the actual central quotient is proved from
the original generation premise. -/
theorem centralQuotient_generated (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (S : Sylow 2 SL(2,F)) (hgen : GeneratedByFixedSpace ρ S) :
    GeneratedByFixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) S := by
  have h := generatedByFixedSpace_of_equivariant_surjection ρ
    (SL2SylowFixedRecognition.centralQuotient ρ) (MonoidHom.id _)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (SL2SylowFixedRecognition.centralQuotient_mk ρ g v).symm) S hgen
  simpa only [Subgroup.map_id] using h

/-- Conditional full-Sylow application to the original local central quotient,
including the exact original quotient map in the intertwining equation. -/
theorem critical_sl2_sylow_central_quotient (Z : Subgroup L) [Z.Normal]
    [IsElementaryAbelian 2 Z] (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L) =
        l * (v.toMul : L) * l⁻¹)
    (S : Sylow 2 SL(2,F)) (hq : IsQuadratic ρ S)
    (hgen : GeneratedByFixedSpace ρ S)
    (hfaith : Function.Injective (SL2SylowFixedRecognition.centralQuotient ρ))
    (hlarge : 4 ≤ Nat.card F) {n : ℕ} (hF : Nat.card F = 2^n)
    (hstrict : Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
      fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) S) < Nat.card S ^ 2) :
    ∃ E : (Additive Z ⧸ centralPart Z) ≃ₗ[ZMod 2] (Fin 2 → F),
      IsSourceNatural (SL2SylowFixedRecognition.centralQuotient ρ) S n ∧
      (SL2SylowFixedRecognition.centralQuotient ρ).IsIrreducible ∧
      Nat.card (fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) S) = Nat.card F ∧
      (∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 →
        fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) (zpowers t) =
          fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) S) ∧
      (∀ v w : Additive Z ⧸ fixedSpace ρ ⊤, v ≠ 0 → w ≠ 0 →
        ∃ l : L, SL2SylowFixedRecognition.centralQuotient ρ
          (e (QuotientGroup.mk' (pCore 2 L) l)) v = w) ∧
      ∀ (l : L) (z : Z),
        E ((centralPart Z).mkQ (Additive.ofMul
          ⟨l*z.val*l⁻¹,(inferInstance : Z.Normal).conj_mem z z.property l⟩)) =
        Matrix.mulVec (e (QuotientGroup.mk' (pCore 2 L) l)).val
          (E ((centralPart Z).mkQ (Additive.ofMul z))) := by
  let : Finite (Additive Z ⧸ fixedSpace ρ ⊤) :=
    Finite.of_surjective _ (fixedSpace ρ ⊤).mkQ_surjective
  let σ := SL2SylowFixedRecognition.centralQuotient ρ
  have hqQ : IsQuadratic σ S := quadratic_of_equivariant_surjection ρ σ
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (SL2SylowFixedRecognition.centralQuotient_mk ρ g v).symm) S hq
  obtain ⟨E,hE⟩ := (sl2_sylow_bound_and_recognition σ hfaith S hqQ
    (centralQuotient_generated Z ρ S hgen)
    (SL2SylowFixedRecognition.centralQuotient_fixed_eq_bot ρ hlarge) hF).2 hstrict
  let c := Submodule.quotEquivOfEq (centralPart Z) (fixedSpace ρ ⊤)
    (centralPart_eq_fixedSpace Z e ρ hact)
  have hfixed := sl2_natural_fixed_spaces σ S hqQ
    (centralQuotient_generated Z ρ S hgen)
    (SL2SylowFixedRecognition.centralQuotient_fixed_eq_bot ρ hlarge) E
  refine ⟨c.trans E,sourceNatural_of_coordinates σ hfaith S hqQ E hF,
    irreducible_of_natural_coordinates σ E hE,hfixed.1,hfixed.2,?_,?_⟩
  · intro v w hv hw
    obtain ⟨g,hg⟩ := transitive_of_natural_coordinates σ E hE hv hw
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    refine ⟨l,?_⟩
    change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
    change σ (e (QuotientGroup.mk' (pCore 2 L) l)) v = w
    rw [hl]
    exact hg
  intro l z
  change E ((fixedSpace ρ ⊤).mkQ (Additive.ofMul
    ⟨l*z.val*l⁻¹,(inferInstance : Z.Normal).conj_mem z z.property l⟩)) = _
  have he : Additive.ofMul (⟨l*z.val*l⁻¹,
      (inferInstance : Z.Normal).conj_mem z z.property l⟩ : Z) =
      ρ (e (QuotientGroup.mk' (pCore 2 L) l)) (Additive.ofMul z) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (hact l (Additive.ofMul z)).symm
  rw [he]
  exact hE (e (QuotientGroup.mk' (pCore 2 L) l)) ((fixedSpace ρ ⊤).mkQ (Additive.ofMul z))

end CFSG.Quasithin.DGS85.ModuleApplications
