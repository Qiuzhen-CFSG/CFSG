module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.LinearSuzuki.Reduction
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear

/-!
# Quadratic Cartan rigidity for binary PSL₂

Semilinear coverage writes the given automorphism as inner times field. After
Sylow conjugacy, root preservation places the inner factor in the standard
Borel. On its literal root quotient the action is therefore precisely the
coefficient action on all field units. The quadratic field calculation kills
that action, and the complement's trivial intersection with the root group
kills the original displacements.

The coverage and quotient calculations include the field of two elements.
Source: Aschbacher–Smith, F.1.3(5), printed p.260, final paragraph.
-/

public section
open scoped MatrixGroups
open Subgroup Atlas
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
namespace CFSG.Quasithin.ChapterF.Source

private theorem coefficient_action_eq {F : Type*} [Field F] [CharP F 2]
    (σ : F ≃+* F) : Theory.PSL2.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g, rfl⟩ := Theory.PSL2.quotientMap_surjective F x
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

/-- Intrinsic Cartan rigidity for the actual binary projective matrix group. -/
theorem cartanQuadraticRigidity_psl2 (F : Type*) [Field F] [Finite F] [CharP F 2] :
    CartanQuadraticRigidity (PSL(2,F)) := by
  apply CartanQuadraticRigidity.of_standard (kernel F) (Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F) (normalizer_kernel F)
  · intro T
    obtain ⟨c, hc, _⟩ := sylow_normalizer_conjugate F T
    exact ⟨(MulAut.conj c).symm,
      (map_symm_eq_iff_map_eq (kernel F) (e := MulAut.conj c)).mpr hc⟩
  · intro D hDB _ hd hs a _ haU haD hquad
    obtain ⟨g, σ, hg⟩ := Theory.PSL2.semilinear_coverage a
    rw [coefficient_action_eq] at hg
    have hgB : g ∈ Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F := inner_factor_mem_borel F g σ (hg ▸ haU)
    let b := borelActor F ⟨g, hgB⟩ σ
    apply MonoidHom.fixes_complement_of_quadratic_field_quotient
      (kernel F) (Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F) D le_sup_left hDB hd hs
      (torusProjection F) (torusProjection_surjective F)
      (by ext x; exact torusProjection_eq_one_iff F x)
      a.toMonoidHom b.toMonoidHom
      (fun x => (borelActor_apply_coe F ⟨g, hgB⟩ σ x).trans
        (MulEquiv.congr_fun hg.symm x)) σ
      (torusProjection_borelActor F ⟨g, hgB⟩ σ)
      (fun x hx => haD ▸ mem_map_of_mem a.toMonoidHom hx) hquad

/-- The linear source alternative, transported along its actual model witness. -/
theorem cartanQuadraticRigidity_linear {H : Type*} [Group H] [Finite H]
    (n : ℕ) (_hn : 0 < n) (h : ClassicalGroup.IsPSL H 2 (2 ^ n)) :
    CartanQuadraticRigidity H := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact CartanQuadraticRigidity.of_equiv e (cartanQuadraticRigidity_psl2 F)

end CFSG.Quasithin.ChapterF.Source
