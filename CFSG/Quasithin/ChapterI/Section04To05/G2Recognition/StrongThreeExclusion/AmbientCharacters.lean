module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.SpecialSupport
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.LocalCharacters
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.CharacterExtraction
public import Theory.Character.NilpotentBrauerIdeal

/-!
# Actual ambient characters in the original Sylow-nine branch

The four local rows are constructed from the literal quaternion quotient.
Their induced virtual characters satisfy the Gram identities by the actual
three-singular transporter control. Thus five distinct nonprincipal ambient
irreducibles and their exact signed induction identities exist without any
character or block input.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour LocalCharacters StrongThreeExclusion
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem induced_generalized (i : Fin 4) :
    IsGeneralizedCharacter (inducedClassFunction c.H (localAlpha c i)) := by
  obtain ⟨a,b,ha,hb,he⟩ := localAlpha_generalized c i
  rw [he]
  exact ⟨_,_,BrauerInduction.inducedClassFunction_isCharacter c.H ha,
    BrauerInduction.inducedClassFunction_isCharacter c.H hb,
    (inducedClassFunctionIntLinear c.H).map_sub a b⟩

private theorem induced_one (i : Fin 4) : inducedClassFunction c.H (localAlpha c i) 1 = 0 := by
  classical
  unfold inducedClassFunction
  simp only [mul_one, inv_mul_cancel, dif_pos c.H.one_mem]
  change (Nat.card c.H : ℂ)⁻¹ * (∑ _g : G, localAlpha c i 1) = 0
  simp only [localAlpha_one, Finset.sum_const_zero, mul_zero]

private theorem principal_inner : scalarProduct G (1 : ClassFunction G) 1 = 1 := by
  simp only [scalarProduct, Pi.one_apply, star_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ (by exact_mod_cast (Nat.card_pos (α := G)).ne')

/-- The original small-Sylow configuration constructs all five nonprincipal
irreducibles, their distinctness, and the signed induction identities. -/
theorem exists_original_ambient_characters (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) :
    ∃ (ε : ℤ) (ψ : ClassFunction G) (μ : Fin 4 → ClassFunction G),
      (ε = 1 ∨ ε = -1) ∧ IsIrreducibleCharacter ψ ∧
      (∀ i, IsIrreducibleCharacter (μ i)) ∧ Function.Injective μ ∧
      (∀ i, ψ ≠ μ i) ∧ ψ ≠ 1 ∧ (∀ i, μ i ≠ 1) ∧
      ∀ i, inducedClassFunction c.H (localAlpha c i) = 1 + (ε : ℂ) • (ψ - μ i) := by
  classical
  let α := fun i => inducedClassFunction c.H (localAlpha c i)
  let β := fun i => α i - 1
  have ha1 (i : Fin 4) : scalarProduct G (α i) 1 = 1 := by
    rw [scalarProduct_inducedClassFunction c.H _ (by intro x g; rfl)]
    convert localAlpha_principal c i using 1
    congr 1
    exact Subsingleton.elim _ _
  have h1a (i : Fin 4) : scalarProduct G 1 (α i) = 1 := by
    rw [← scalarProduct_conj, ha1, star_one]
  have haa (i k : Fin 4) : scalarProduct G (α i) (α k) = 2 + if i = k then 1 else 0 :=
    (three_singular_induction_isometry c hsmall _ _ (localAlpha_generalized c k).isClassFunction
      (localAlpha_supported c i) (localAlpha_supported c k)).trans (localAlpha_inner c i k)
  have hb (i : Fin 4) : IsGeneralizedCharacter (β i) :=
    (induced_generalized c i).sub isCharacter_one.isGeneralized
  have hbp (i k : Fin 4) : scalarProduct G (β i) (β k) = 1 + if i = k then 1 else 0 := by
    change scalarProduct G (α i - 1) (α k - 1) = _
    rw [scalarProduct_sub_left]
    have hsub (f g : ClassFunction G) : scalarProduct G f (g - 1) =
        scalarProduct G f g - scalarProduct G f 1 := by
      rw [← scalarProduct_conj (g - 1), scalarProduct_sub_left]
      simp only [star_sub, scalarProduct_conj]
    rw [hsub, hsub, haa, ha1, h1a, principal_inner]
    ring
  obtain ⟨ε,ψ,μ,hε,hψ,hμ,hi,hd,hψ1,hμ1,he⟩ := exists_common_irreducible_of_four_rows β hb
    (fun i => by change inducedClassFunction c.H (localAlpha c i) 1 - 1 = -1; rw [induced_one]; ring) hbp
    (fun i => by change scalarProduct G (α i - 1) 1 = 0
                 rw [scalarProduct_sub_left, ha1, principal_inner, sub_self])
  refine ⟨ε,ψ,μ,hε,hψ,hμ,hi,hd,hψ1,hμ1,fun i => ?_⟩
  have hh := he i
  change α i - 1 = _ at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
