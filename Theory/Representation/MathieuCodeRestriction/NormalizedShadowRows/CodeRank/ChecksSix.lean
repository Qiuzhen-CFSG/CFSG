module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRank.Data
/-! Kernel checks for the six-dimensional displacement certificates.
Source: Aschbacher--Smith H.16.5, printed p.404. -/
public section
namespace MathieuCode.NormalizedShadowRows.CodeRank
set_option maxRecDepth 4096

private theorem check_00 : ∀ a : Fin 8, checkRow 0 ⟨8*0+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_01 : ∀ a : Fin 8, checkRow 0 ⟨8*1+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_02 : ∀ a : Fin 8, checkRow 0 ⟨8*2+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_03 : ∀ a : Fin 8, checkRow 0 ⟨8*3+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_04 : ∀ a : Fin 8, checkRow 0 ⟨8*4+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_05 : ∀ a : Fin 8, checkRow 0 ⟨8*5+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_06 : ∀ a : Fin 8, checkRow 0 ⟨8*6+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_07 : ∀ a : Fin 8, checkRow 0 ⟨8*7+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_08 : ∀ a : Fin 8, checkRow 0 ⟨8*8+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_09 : ∀ a : Fin 8, checkRow 0 ⟨8*9+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_10 : ∀ a : Fin 8, checkRow 0 ⟨8*10+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_11 : ∀ a : Fin 8, checkRow 0 ⟨8*11+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_12 : ∀ a : Fin 8, checkRow 0 ⟨8*12+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_13 : ∀ a : Fin 8, checkRow 0 ⟨8*13+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_14 : ∀ a : Fin 8, checkRow 0 ⟨8*14+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_15 : ∀ a : Fin 8, checkRow 0 ⟨8*15+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_16 : ∀ a : Fin 8, checkRow 0 ⟨8*16+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_17 : ∀ a : Fin 8, checkRow 0 ⟨8*17+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_18 : ∀ a : Fin 8, checkRow 0 ⟨8*18+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_19 : ∀ a : Fin 8, checkRow 0 ⟨8*19+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_20 : ∀ a : Fin 8, checkRow 0 ⟨8*20+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_21 : ∀ a : Fin 8, checkRow 0 ⟨8*21+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_22 : ∀ a : Fin 8, checkRow 0 ⟨8*22+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem check_23 : ∀ a : Fin 8, checkRow 0 ⟨8*23+a.val, by omega⟩ := by
  unfold checkRow
  decide +kernel

/-- Every same-color commuting pair has the certified independent columns. -/
theorem six_checked (v : Fin 192) : checkRow 0 v := by
  have blocks : ∀ (b : Fin 24) (a : Fin 8), checkRow 0 ⟨8*b.val+a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact check_00
    · exact check_01
    · exact check_02
    · exact check_03
    · exact check_04
    · exact check_05
    · exact check_06
    · exact check_07
    · exact check_08
    · exact check_09
    · exact check_10
    · exact check_11
    · exact check_12
    · exact check_13
    · exact check_14
    · exact check_15
    · exact check_16
    · exact check_17
    · exact check_18
    · exact check_19
    · exact check_20
    · exact check_21
    · exact check_22
    · exact check_23
  have h := blocks ⟨v.val/8, by omega⟩ ⟨v.val%8, by omega⟩
  have he : (⟨8*(v.val/8)+v.val%8, by omega⟩ : Fin 192) = v := by
    apply Fin.ext
    change 8*(v.val/8)+v.val%8 = v.val
    omega
  rw [he] at h
  exact h
end MathieuCode.NormalizedShadowRows.CodeRank
