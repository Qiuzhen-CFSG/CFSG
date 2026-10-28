module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.StrictM22Cocode.Data
/-! Kernel-checked left inverses for the literal M22 cocode quotient displacements. -/
@[expose] public section
namespace MathieuCode.QuadraticActors.StrictM22Cocode
set_option maxRecDepth 4096

private theorem check_00 : ∀ a : Fin 8, checkRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_01 : ∀ a : Fin 8, checkRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_02 : ∀ a : Fin 8, checkRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_03 : ∀ a : Fin 8, checkRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_04 : ∀ a : Fin 8, checkRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_05 : ∀ a : Fin 8, checkRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_06 : ∀ a : Fin 8, checkRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_07 : ∀ a : Fin 8, checkRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_08 : ∀ a : Fin 8, checkRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

/-- Each relevant native pair has five independent quotient-displacement columns. -/
theorem certificate_check (v w : Fin 72) (hv : v ≠ 0) (hw : w ≠ 0)
    (hne : v ≠ w) (ha : outerAdjacent v w = true) :
    leftInverse v w * selected v w = 1 := by
  have blocks : ∀ k : Fin 9, ∀ a : Fin 8, checkRow ⟨8 * k.val + a.val, by omega⟩ := by
    intro k
    fin_cases k
    · exact check_00
    · exact check_01
    · exact check_02
    · exact check_03
    · exact check_04
    · exact check_05
    · exact check_06
    · exact check_07
    · exact check_08
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 72) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  rw [he] at h
  exact h w hv hw hne ha
end MathieuCode.QuadraticActors.StrictM22Cocode
