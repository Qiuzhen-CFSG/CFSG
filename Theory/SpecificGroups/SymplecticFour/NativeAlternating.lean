module
public import Theory.SpecificGroups.SymplecticFour.SevenNormalizer
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Alternating rows in a four-dimensional symplectic action

The seven-cycle and its multiplier-two normalizer lie in both A₇ and A₈.
Their images contradict the symplectic order-seven spectral obstruction in
characteristic two. Among nonsolvable alternating groups of degree at most
eight, a faithful four-dimensional symplectic action therefore leaves A₅ or
A₆. The last theorem applies the exclusion to the actual supplied carrier
and representation, as needed in the alternating row of Theorem C.

Source: Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.NativeAlternating

private def a7 : alternatingGroup (Fin 7) := ⟨
  ⟨![1,2,3,4,5,6,0], ![6,0,1,2,3,4,5], by decide, by decide⟩, by change Equiv.Perm.sign _ = 1; decide +kernel⟩
private def b7 : alternatingGroup (Fin 7) := ⟨
  ⟨![0,2,4,6,1,3,5], ![0,4,1,5,2,6,3], by decide, by decide⟩, by change Equiv.Perm.sign _ = 1; decide +kernel⟩
private def a8 : alternatingGroup (Fin 8) := ⟨
  ⟨![1,2,3,4,5,6,0,7], ![6,0,1,2,3,4,5,7], by decide, by decide⟩, by change Equiv.Perm.sign _ = 1; decide +kernel⟩
private def b8 : alternatingGroup (Fin 8) := ⟨
  ⟨![0,2,4,6,1,3,5,7], ![0,4,1,5,2,6,3,7], by decide, by decide⟩, by change Equiv.Perm.sign _ = 1; decide +kernel⟩

variable {F : Type*} [Field F] [CharP F 2]
/-- The order-seven normalizer excludes A₇ from Sp₄ in characteristic two. -/
theorem alternatingSeven_not_injective (j : alternatingGroup (Fin 7) →* Sp F) :
    ¬ Function.Injective j := by
  intro hj
  apply SevenNormalizer.seven_not_conjugate_square (j a7) (j b7)
  · rw [←map_pow, show a7^7=1 by decide +kernel, map_one]
  · exact fun h => (by decide +kernel : a7≠1) (hj (h.trans j.map_one.symm))
  · simpa only [map_mul,map_inv,map_pow] using
      congrArg j (by decide +kernel : b7*a7*b7⁻¹=a7^2)

/-- The same normalizer excludes A₈. -/
theorem alternatingEight_not_injective (j : alternatingGroup (Fin 8) →* Sp F) :
    ¬ Function.Injective j := by
  intro hj
  apply SevenNormalizer.seven_not_conjugate_square (j a8) (j b8)
  · rw [←map_pow, show a8^7=1 by decide +kernel, map_one]
  · exact fun h => (by decide +kernel : a8≠1) (hj (h.trans j.map_one.symm))
  · simpa only [map_mul,map_inv,map_pow] using
      congrArg j (by decide +kernel : b8*a8*b8⁻¹=a8^2)

/-- The actual alternating carrier of degree at most eight is A₅ or A₆. -/
theorem alternating_model_five_or_six {H : Type*} [Group H]
    (hns : ¬ Group.IsSolvable H) {n : ℕ} (hn : n≤8)
    (e : H ≃* alternatingGroup (Fin n)) (j : H →* Sp F) (hj : Function.Injective j) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 6)) := by
  have hsmall : ¬ n≤4 := by
    intro hn4
    have hs : Group.IsSolvable (alternatingGroup (Fin n)) := by
      by_cases h4 : n=4
      · subst n
        exact alternatingGroup_fin_four_isSolvable
      · letI := alternatingGroup.isMulCommutative_of_card_le_three
          (α:=Fin n) (by simpa using (show n≤3 by omega))
        exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
    letI := hs
    exact hns (Group.isSolvable_of_isSolvable_injective (f:=e.toMonoidHom) e.injective)
  have hj' : Function.Injective (j.comp e.symm.toMonoidHom) := hj.comp e.symm.injective
  have hn7 : n≠7 := by
    rintro rfl
    exact alternatingSeven_not_injective _ hj'
  have hn8 : n≠8 := by
    rintro rfl
    exact alternatingEight_not_injective _ hj'
  have he : n=5 ∨ n=6 := by omega
  rcases he with rfl | rfl
  · exact .inl ⟨e⟩
  · exact .inr ⟨e⟩
end Theory.SpecificGroups.SymplecticFour.NativeAlternating
