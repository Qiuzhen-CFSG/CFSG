module

public import Glauberman.DicksonExceptionalF9
public import GorensteinWalter.A5
public import BenderSuzuki.MatrixGroups.PSL2
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# An alternating subgroup in PSL₂(9)

The certified exceptional embedding of SL₂(5) into SL₂(9) preserves `-1`.
Since the center of SL₂(5) consists of `1` and `-1`, the embedding descends
to the projective groups. Injectivity reflects centrality, so the descended
map is injective. Composing with the exceptional isomorphism A₅ ≃ PSL₂(5)
and a finite-field isomorphism gives an actual A₅ subgroup of PSL₂(9).

Source: the exceptional subgroup in Dickson's classification, used in
Thompson's minimal-simple parameter argument (roadmap M4).
-/

namespace Glauberman.Dickson

open BenderSuzuki.MatrixGroups Matrix

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance : Fact (∀ r : ZMod 3, r ^ 2 ≠ (-1 : ZMod 3) + 0 * r) :=
  ⟨by decide⟩

local instance : Fintype ExceptionalF9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3)
    (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm

private theorem exceptionalHom_center :
    Subgroup.center ExceptionalSL5 ≤
      (Subgroup.center ExceptionalSL9).comap exceptionalHom := by
  intro g hg
  obtain ⟨a, ha, h⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  simp only [Fintype.card_fin] at ha
  have hg' : g = 1 ∨ g = -1 := by
    rcases sq_eq_one_iff.mp ha with rfl | rfl
    · left
      apply Subtype.ext
      simpa using h.symm
    · right
      apply Subtype.ext
      simpa [← Matrix.diagonal_neg] using h.symm
  change exceptionalHom g ∈ Subgroup.center ExceptionalSL9
  rcases hg' with rfl | rfl
  · simp
  · rw [exceptionalHom_neg_one, Subgroup.mem_center_iff]
    intro x
    simp

private def exceptionalPSLHom :
    PSL2MatrixGroup (ZMod 5) →* PSL2MatrixGroup ExceptionalF9 :=
  QuotientGroup.map _ _ exceptionalHom exceptionalHom_center

private theorem exceptionalPSLHom_injective :
    Function.Injective exceptionalPSLHom := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | _ a =>
    induction y using QuotientGroup.induction_on with
    | _ b =>
      apply QuotientGroup.eq.mpr
      have hc : exceptionalHom (a⁻¹ * b) ∈ Subgroup.center ExceptionalSL9 := by
        simpa only [map_mul, map_inv] using QuotientGroup.eq.mp hxy
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro g
      apply exceptionalHom_injective
      simpa only [map_mul] using hc (exceptionalHom g)

/-- An actual injective homomorphism from A₅ into PSL₂ over the field of nine elements. -/
public theorem exists_alternatingGroupFive_embedding_psl2_nine :
    ∃ f : alternatingGroup (Fin 5) →* PSL2MatrixGroup (GaloisField 3 2),
      Function.Injective f := by
  let : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card ExceptionalF9 = Fintype.card (GaloisField 3 2) := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0)]
    norm_num [Fintype.card_prod, ← Nat.card_eq_fintype_card, GaloisField.card]
  let e := FiniteField.ringEquivOfCardEq hcard
  let eSL := specialLinearMapEquiv e
  let ePSL : PSL2MatrixGroup ExceptionalF9 ≃* PSL2MatrixGroup (GaloisField 3 2) :=
    QuotientGroup.congr _ _ eSL (by
      ext A
      constructor
      · rintro ⟨B, hB, rfl⟩
        exact (MulEquivClass.apply_mem_center_iff eSL).2 hB
      · intro hA
        refine ⟨eSL.symm A, ?_, eSL.apply_symm_apply A⟩
        exact (MulEquivClass.apply_mem_center_iff eSL.symm).2 hA)
  obtain ⟨eA⟩ := GorensteinWalter.alternatingGroupFive_equiv_PSL2
  refine ⟨ePSL.toMonoidHom.comp (exceptionalPSLHom.comp eA.toMonoidHom), ?_⟩
  exact ePSL.injective.comp (exceptionalPSLHom_injective.comp eA.injective)

end

end Glauberman.Dickson
