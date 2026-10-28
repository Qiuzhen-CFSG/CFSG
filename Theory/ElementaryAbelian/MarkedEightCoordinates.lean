module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coordinates adapted to an actual elementary-eight flag

Choose a nonidentity element of the point, a plane element outside the point,
and a vector outside the plane. They are linearly independent in the canonical
binary vector space. Its order gives dimension three, so these vectors form a
basis. Containment and the orders two and four identify the images of both
coordinate subgroups under the same multiplicative equivalence.

Source: Aschbacher--Smith, Notation 12.8.2 and 14.4.8(1), pp.849,1009.
-/

public section

open Matrix Subgroup
open scoped IsMulCommutative
namespace Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag

variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- One coordinate map respects both members of the given flag. -/
theorem coordinates (hE : Nat.card E = 8) (A B : Subgroup E)
    (hA : Nat.card A = 2) (hB : Nat.card B = 4) (hAB : A ≤ B) :
    ∃ e : Model ≃* E, point.map e.toMonoidHom = A ∧ plane.map e.toMonoidHom = B := by
  classical
  let : AddCommGroup (Additive E) := inferInstance
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hE, show (2 : ℕ) ^ 3 = 8 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive E) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  have hA0 : A ≠ ⊥ := by intro he; rw [he, Subgroup.card_bot] at hA; omega
  have hAB' : A < B := lt_of_le_of_ne hAB (by intro he; rw [he, hB] at hA; omega)
  have hBtop : B < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he; rw [he, Subgroup.card_top, hE] at hB; omega)
  obtain ⟨a, ha, ha0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hA0)
  obtain ⟨b, hb, hbA⟩ := SetLike.exists_of_lt hAB'
  obtain ⟨c, _, hcB⟩ := SetLike.exists_of_lt hBtop
  let U : Submodule (ZMod 2) (Additive E) := AddSubgroup.toZModSubmodule 2 A.toAddSubgroup
  let W : Submodule (ZMod 2) (Additive E) := AddSubgroup.toZModSubmodule 2 B.toAddSubgroup
  let a' : Additive E := Additive.ofMul a
  let b' : Additive E := Additive.ofMul b
  let c' : Additive E := Additive.ofMul c
  have ha' : a' ∈ U := ha
  have haW : a' ∈ W := hAB ha
  have hb' : b' ∈ W := hb
  have ha0' : a' ≠ 0 := ha0
  have hli2 : LinearIndependent (ZMod 2) ![a', b'] := by
    apply (LinearIndependent.pair_iff' ha0').mpr
    intro t he
    exact hbA (show b' ∈ U from he ▸ U.smul_mem t ha')
  have hspan : Submodule.span (ZMod 2) (Set.range ![a', b']) ≤ W := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact haW
    · exact hb'
  have hli : LinearIndependent (ZMod 2) ![a', b', c'] := by
    have hs := hli2.finSnoc (x := c') (fun hh => hcB (hspan hh))
    have hf : ![a', b', c'] = Fin.snoc ![a', b'] c' := by
      ext i
      fin_cases i <;> rfl
    rw [hf]
    exact hs
  let d := basisOfLinearIndependentOfCardEqFinrank hli
    (by simpa only [Fintype.card_fin] using hdim.symm)
  let e : Model ≃* E := d.equivFun.symm.toAddEquiv.toMultiplicativeLeft
  have he (v : Model) : Additive.ofMul (e v) =
      v.toAdd 0 • a' + v.toAdd 1 • b' + v.toAdd 2 • c' := by
    change d.equivFun.symm v.toAdd = _
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_three]
    simp [d]
  refine ⟨e, ?_, ?_⟩
  · apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨v, hv, rfl⟩
      change Additive.ofMul (e v) ∈ U
      rw [he]
      change v.toAdd 1 = 0 ∧ v.toAdd 2 = 0 at hv
      simpa only [hv.1, hv.2, zero_smul, add_zero] using U.smul_mem (v.toAdd 0) ha'
    · rw [← Nat.card_congr (point.equivMapOfInjective e.toMonoidHom e.injective).toEquiv,
        card_point, hA]
  · apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨v, hv, rfl⟩
      change Additive.ofMul (e v) ∈ W
      rw [he]
      change v.toAdd 2 = 0 at hv
      simpa only [hv, zero_smul, add_zero] using
        W.add_mem (W.smul_mem (v.toAdd 0) haW) (W.smul_mem (v.toAdd 1) hb')
    · rw [← Nat.card_congr (plane.equivMapOfInjective e.toMonoidHom e.injective).toEquiv,
        card_plane, hB]
end Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
