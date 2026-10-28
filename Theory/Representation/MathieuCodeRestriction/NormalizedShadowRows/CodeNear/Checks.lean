module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeNear.Data
/-! Kernel checks for the anchored M22 code displacement calculation.
Source: Aschbacher--Smith H.16.5, printed p.404, refs/quasithin.pdf. -/
public section
namespace MathieuCode.NormalizedShadowRows.CodeNear
set_option maxRecDepth 4096
set_option Elab.async false

private theorem block0 : ∀ a : Fin 8, checkRow ⟨8*0+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block1 : ∀ a : Fin 8, checkRow ⟨8*1+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block2 : ∀ a : Fin 8, checkRow ⟨8*2+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block3 : ∀ a : Fin 8, checkRow ⟨8*3+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block4 : ∀ a : Fin 8, checkRow ⟨8*4+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block5 : ∀ a : Fin 8, checkRow ⟨8*5+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block6 : ∀ a : Fin 8, checkRow ⟨8*6+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block7 : ∀ a : Fin 8, checkRow ⟨8*7+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

private theorem block8 : ∀ a : Fin 8, checkRow ⟨8*8+a.val,by omega⟩ := by
  unfold checkRow
  decide +kernel

theorem checked (v : Fin 72) : checkRow v := by
  have blocks : ∀ k : Fin 9, ∀ a : Fin 8, checkRow ⟨8*k.val+a.val,by omega⟩ := by
    intro k
    fin_cases k
    · exact block0
    · exact block1
    · exact block2
    · exact block3
    · exact block4
    · exact block5
    · exact block6
    · exact block7
    · exact block8
  have h := blocks ⟨v.val/8,by omega⟩ ⟨v.val%8,by omega⟩
  have he : (⟨8*(v.val/8)+v.val%8,by omega⟩ : Fin 72) = v := by
    apply Fin.ext
    change 8*(v.val/8)+v.val%8 = v.val
    omega
  rwa [he] at h
end MathieuCode.NormalizedShadowRows.CodeNear
