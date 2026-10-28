module

public import Theory.Mathieu.LargeInvolutionGeneration.Certificates23

/-!
# Checked four-involution generation words in M24

For each of the two marked involutions, the checked words recover the three
native generators of the M23 point stabilizer and an element moving its fixed
point. The actual extension map is used when comparing the point tables.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
manuscript p.17.
-/

public section
namespace Sporadic.Mathieu.LargeInvolutionGeneration
set_option maxRecDepth 10000

 theorem letter24_apply (i : Fin 3) (x : Fin 24) :
    (letter24 i).val x = letterPoint24 i x := by
  revert i x
  decide +kernel

 theorem representative24_apply (k : Fin 2) (x : Fin 24) :
    (representative24 k).val x = representativePoint24 k x := by
  revert k x
  decide +kernel

private theorem targetPoint24_embedding (i : Fin 3) (x : Fin 23) :
    targetPoint24 i.castSucc (m23PointEmbedding x) =
      m23PointEmbedding (targetPoint23 i x) := by
  simp only [m23PointEmbedding_apply]
  revert i x
  decide +kernel

 theorem target24_apply (i : Fin 4) (x : Fin 24) :
    (target24 i).val x = targetPoint24 i x := by
  have he (j : Fin 3) : target24 j.castSucc = embedding (target23 j) := by
    fin_cases j <;> rfl
  have hfirst (j : Fin 3) : (target24 j.castSucc).val x = targetPoint24 j.castSucc x := by
    rw [he]
    by_cases hx : x = 0
    · subst x
      have hz : targetPoint24 j.castSucc 0 = 0 := by
        revert j
        decide +kernel
      rw [hz]
      exact m23ExtendHom_apply_24 _
    · obtain ⟨y, hy⟩ := m23PointEquiv.surjective ⟨x, hx⟩
      have hemb : m23PointEmbedding y = x := congrArg Subtype.val hy
      rw [← hemb]
      change m23ExtendHom (target23 j) (m23PointEmbedding y) = _
      rw [m23ExtendHom_apply_embedded, target23_apply, targetPoint24_embedding]
  fin_cases i
  · exact hfirst 0
  · exact hfirst 1
  · exact hfirst 2
  · exact letter24_apply 0 x

 theorem conjugator24_apply (k : Fin 2) (i : Fin 4) (x : Fin 24) :
    (conjugator24 k i).val x = conjugatorPoint24 k i x := by
  rw [conjugator24, evalWord_apply _ _ letter24_apply]
  revert k i x
  decide +kernel

private theorem conjugate24_relation (k : Fin 2) (i : Fin 4) (x : Fin 24) :
    conjugatePoint24 k i (conjugatorPoint24 k i x) =
      conjugatorPoint24 k i (representativePoint24 k x) := by
  revert k i x
  decide +kernel

 theorem conjugate24_apply (k : Fin 2) (i : Fin 4) (x : Fin 24) :
    (conjugate24 k i).val x = conjugatePoint24 k i x := by
  obtain ⟨y, rfl⟩ := (conjugator24 k i).val.surjective x
  change (conjugator24 k i).val ((representative24 k).val
    ((conjugator24 k i).val.symm ((conjugator24 k i).val y))) = _
  rw [Equiv.symm_apply_apply, representative24_apply, conjugator24_apply,
    conjugator24_apply, conjugate24_relation]

private theorem generationPoint24 (k : Fin 2) (i : Fin 4) (x : Fin 24) :
    wordPoint (conjugatePoint24 k) (generationWord24 k i) x = targetPoint24 i x := by
  revert k i x
  decide +kernel

/-- Each involution class recovers generators of the full native M24. -/
theorem generation24 (k : Fin 2) (i : Fin 4) :
    evalWord (conjugate24 k) (generationWord24 k i) = target24 i := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [evalWord_apply _ _ (conjugate24_apply k), generationPoint24, target24_apply]

end Sporadic.Mathieu.LargeInvolutionGeneration
