module
public import Theory.Representation.RankOne.QuadraticRecognition.Generation
public import Theory.Representation.SL2SylowFixedRecognition.Complementary
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!+# The full-Sylow branch of quadratic rank-one recognition

For SL₂ over an arbitrary finite binary field of positive degree,
quadratic Sylow action, zero global fixed space and the corrected fixed-space
generation condition imply a direct sum of natural modules. The strict
DGS85 (5.12) inequality forces exactly one copy. The original field and
matrix actors are retained by an equivariant linear equivalence.

The proof uses odd-index averaging and complementary quadratic fixed spaces,
then the existing root-coordinate reconstruction. This is the full-Sylow
case in DGS85, printed pp.113--114; proper actors and the other rank-one
families require further arguments.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite V] in
/-- Every distinct Sylow pair has complementary fixed spaces under the
corrected generation hypothesis. -/
theorem sl2_sylow_fixed_isCompl (ρ : Representation (ZMod 2) SL(2,F) V)
    (S T : Sylow 2 SL(2,F)) (hST : S ≠ T)
    (hq : IsQuadratic ρ S) (hgen : GeneratedByFixedSpace ρ S)
    (hfix : fixedSpace ρ ⊤ = ⊥) :
    IsCompl (fixedSpace ρ S) (fixedSpace ρ T) := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) S T
  have hg : g ∉ normalizer (S : Set SL(2,F)) := by
    intro hg
    exact hST (Sylow.smul_eq_iff_mem_normalizer.mpr hg).symm
  exact fixed_isCompl_of_sylow_generation ρ S _
    (Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer S hg)
    hq (SL2SylowFixedRecognition.quadratic_conjugate ρ hq g) hgen hfix

/-- Quadratic Sylow action and the corrected generation condition produce
natural copies without an irreducibility or semisimplicity assumption. -/
theorem sl2_natural_copies (ρ : Representation (ZMod 2) SL(2,F) V)
    (S : Sylow 2 SL(2,F)) (hq : IsQuadratic ρ S)
    (hgen : GeneratedByFixedSpace ρ S) (hfix : fixedSpace ρ ⊤ = ⊥)
    : SL2SylowFixedRecognition.NaturalCoordinates ρ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) S
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  have hupper : IsQuadratic ρ (Matrix.SpecialLinearGroup.upperUnipotent F) := by
    have hqg := SL2SylowFixedRecognition.quadratic_conjugate ρ hq g
    change IsQuadratic ρ ((g • S : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) at hqg
    rw [hg] at hqg
    exact hqg
  apply SL2SylowFixedRecognition.RootCoordinates.natural_of_quadratic_moved_fixed_free ρ hupper ?_ hfix
  apply top_unique
  apply (moved_eq_top_of_sylow_generation ρ S hgen hfix).ge.trans
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,v⟩,rfl⟩
  exact Submodule.subset_span ⟨a,mem_top a,v,Submodule.mem_top,rfl⟩

private theorem degree_eq_twice_fixedCodim (ρ : Representation (ZMod 2) SL(2,F) V)
    (S : Sylow 2 SL(2,F)) (hq : IsQuadratic ρ S)
    (hgen : GeneratedByFixedSpace ρ S) (hfix : fixedSpace ρ ⊤ = ⊥) :
    Module.finrank (ZMod 2) V = 2 * fixedCodim ρ S := by
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt
    (lt_top_iff_ne_top.mpr (Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S))
  have hST : S ≠ g • S := by
    intro h
    exact hg.2 (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)
  have h := sl2_sylow_fixed_isCompl ρ S (g • S) hST hq hgen hfix
  have hdim := (fixedSpace ρ S).finrank_sup_add_finrank_inf_eq (fixedSpace ρ (g • S : Sylow 2 SL(2,F)))
  rw [h.sup_eq_top,h.inf_eq_bot,finrank_top,finrank_bot,add_zero] at hdim
  have he := (fixedSpaceConjEquiv ρ S g).finrank_eq
  have hc := fixedCodim_add_finrank ρ S
  change Module.finrank (ZMod 2) (fixedSpace ρ S) =
    Module.finrank (ZMod 2) (fixedSpace ρ (g • S : Sylow 2 SL(2,F))) at he
  omega

/-- DGS85 (5.12), for the actual full Sylow in SL₂(2ⁿ), n ≥ 1.
Both the non-strict estimate and strict natural recognition retain the
literal fixed quotient. -/
theorem sl2_sylow_bound_and_recognition (ρ : Representation (ZMod 2) SL(2,F) V)
    (hfaith : Function.Injective ρ) (S : Sylow 2 SL(2,F))
    (hq : IsQuadratic ρ S) (hgen : GeneratedByFixedSpace ρ S)
    (hfix : fixedSpace ρ ⊤ = ⊥) {n : ℕ} (hF : Nat.card F = 2^n) :
    Nat.card S ≤ Nat.card (V ⧸ fixedSpace ρ S) ∧
      (Nat.card (V ⧸ fixedSpace ρ S) < Nat.card S ^ 2 →
        ∃ E : V ≃ₗ[ZMod 2] (Fin 2 → F),
          ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v)) := by
  obtain ⟨m,e,he⟩ := sl2_natural_copies ρ S hq hgen hfix
  have hdimF : Module.finrank (ZMod 2) F = n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF,Nat.card_zmod] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc).symm
  have hdim := e.finrank_eq
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,hdimF] at hdim
  have hcodim := degree_eq_twice_fixedCodim ρ S hq hgen hfix
  have hc : fixedCodim ρ S = m*n := by nlinarith
  have hm : 0 < m := by
    by_contra! hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    have htriv (g : SL(2,F)) : ρ g = ρ 1 := by
      ext v
      apply e.injective
      subst m
      exact Subsingleton.elim _ _
    have hall (g : SL(2,F)) : g = 1 := hfaith (htriv g)
    have hnS : normalizer (S : Set SL(2,F)) = ⊤ := by
      apply top_unique
      intro g _
      rw [hall g]
      exact one_mem _
    exact Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S hnS
  have hS : Nat.card S = 2^n :=
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).toEquiv).symm.trans hF
  have hQ : Nat.card (V ⧸ fixedSpace ρ S) = 2^(m*n) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact congrArg (fun d => 2^d) hc
  constructor
  · rw [hS,hQ]
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)
  · intro hstrict
    rw [hS,hQ,← pow_mul] at hstrict
    have hlt : m*n < n*2 := (Nat.pow_lt_pow_iff_right (by decide)).mp hstrict
    have hm1 : m = 1 := by nlinarith
    subst m
    refine ⟨e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → F)),?_⟩
    intro g v
    exact he g v 0

end Representation.RankOne.QuadraticRecognition
