module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.MathieuExtensions

/-!
# The marked inner parabolics supplement the outer M₁₂ Borel

The actual embedding of M₁₂ into Aut(M₁₂) pulls the two outer parabolics
and their common Borel back to the original marked subgroups. Consequently
each embedded inner parabolic meets the outer Borel in the inner Borel.
Its order is 192, whereas the outer Borel has order 128, so their join has
order 384 and is the entire outer parabolic. The inner parabolic has index
two there and is normal. These are the literal model inputs for gluing
normal-base extensions in Goldschmidt, §3.8, and Aschbacher--Smith F.1.12,
cases (12)--(13), printed p.263.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase.ModelProducts
open Theory.GroupTheory Sporadic.Mathieu

/-- The original marked endpoint embedded by actual inner conjugation. -/
def innerP (i : Fin 2) : Subgroup (MulAut M12) :=
  (MathieuTwelve.P i).map MulAut.conj

/-- The original marked Borel embedded by actual inner conjugation. -/
def innerB : Subgroup (MulAut M12) := MathieuTwelve.B.map MulAut.conj

/-- Faithfulness of inner conjugation follows from the already marked inner model. -/
theorem conj_injective : Function.Injective (MulAut.conj : M12 →* MulAut M12) := by
  intro x y h
  apply M12ExceptionalExtension.innerModel.embedding_injective
  apply AutMathieuTwelve.ambientEquiv.injective
  simpa only [AutMathieuTwelve.ambientEquiv_inner] using h

private theorem conj_eq_comp : (MulAut.conj : M12 →* MulAut M12) =
    AutMathieuTwelve.ambientEquiv.toMonoidHom.comp
      M12ExceptionalExtension.innerModel.embedding := by
  apply MonoidHom.ext
  intro x
  exact (AutMathieuTwelve.ambientEquiv_inner x).symm

/-- The original endpoint is the exact inverse image of its outer counterpart. -/
theorem autP_comap_conj (i : Fin 2) :
    (AutMathieuTwelve.autP i).comap MulAut.conj = MathieuTwelve.P i := by
  rw [conj_eq_comp, AutMathieuTwelve.autP, ← Subgroup.comap_comap,
    Subgroup.comap_map_eq_self_of_injective AutMathieuTwelve.ambientEquiv.injective,
    AutMathieuTwelve.P_eq_L, MathieuTwelve.P_eq_L]
  fin_cases i
  · exact M12ExceptionalExtension.SecondCoordinates.comap_firstParabolic
      M12ExceptionalExtension.innerModel
  · exact M12ExceptionalExtension.SecondCoordinates.comap_secondParabolic
      M12ExceptionalExtension.innerModel

/-- The original Borel is the exact inverse image of the outer Borel. -/
theorem autB_comap_conj :
    AutMathieuTwelve.autB.comap MulAut.conj = MathieuTwelve.B := by
  rw [conj_eq_comp, AutMathieuTwelve.autB, ← Subgroup.comap_comap,
    Subgroup.comap_map_eq_self_of_injective AutMathieuTwelve.ambientEquiv.injective,
    AutMathieuTwelve.B_eq_S, MathieuTwelve.B_eq_S]
  exact M12ExceptionalExtension.SecondCoordinates.comap_overlap
    M12ExceptionalExtension.innerModel

theorem innerP_le_autP (i : Fin 2) : innerP i ≤ AutMathieuTwelve.autP i := by
  rw [innerP, Subgroup.map_le_iff_le_comap, autP_comap_conj]

theorem innerB_le_autB : innerB ≤ AutMathieuTwelve.autB := by
  rw [innerB, Subgroup.map_le_iff_le_comap, autB_comap_conj]

/-- The embedded endpoint and outer Borel retain exactly the original overlap. -/
theorem innerP_inf_autB (i : Fin 2) :
    innerP i ⊓ AutMathieuTwelve.autB = innerB := by
  ext a
  constructor
  · rintro ⟨⟨x, _hx, rfl⟩, hb⟩
    refine ⟨x, ?_, rfl⟩
    change x ∈ AutMathieuTwelve.autB.comap MulAut.conj at hb
    rwa [autB_comap_conj] at hb
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, (show MathieuTwelve.B ≤ MathieuTwelve.P i from le_sup_right) hx, rfl⟩, ?_⟩
    change x ∈ AutMathieuTwelve.autB.comap MulAut.conj
    rwa [autB_comap_conj]

private theorem card_innerP (i : Fin 2) : Nat.card (innerP i) = 192 := by
  rw [innerP, Subgroup.card_map_of_injective conj_injective, MathieuTwelve.P_eq_L]
  fin_cases i
  · exact M12SmallPair.card_firstParabolic
  · exact M12SmallPair.card_secondParabolic

private theorem card_autP (i : Fin 2) : Nat.card (AutMathieuTwelve.autP i) = 384 := by
  rw [AutMathieuTwelve.autP,
    Subgroup.card_map_of_injective AutMathieuTwelve.ambientEquiv.injective,
    AutMathieuTwelve.P_eq_L]
  fin_cases i
  · exact M12ExceptionalExtension.FirstParabolic.card_firstParabolic
      M12ExceptionalExtension.innerModel
  · exact M12ExceptionalExtension.SecondCoordinates.card_secondParabolic
      M12ExceptionalExtension.innerModel

private theorem card_autB : Nat.card AutMathieuTwelve.autB = 128 := by
  rw [AutMathieuTwelve.autB,
    Subgroup.card_map_of_injective AutMathieuTwelve.ambientEquiv.injective,
    AutMathieuTwelve.B_eq_S]
  exact M12ExceptionalExtension.SecondCoordinates.card_overlap
    M12ExceptionalExtension.innerModel

/-- The normal inner endpoint has index two in the actual outer endpoint. -/
theorem innerP_index (i : Fin 2) :
    ((innerP i).subgroupOf (AutMathieuTwelve.autP i)).index = 2 := by
  have hc : Nat.card ((innerP i).subgroupOf (AutMathieuTwelve.autP i)) = 192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerP_le_autP i)).toEquiv,
      card_innerP]
  have h := ((innerP i).subgroupOf (AutMathieuTwelve.autP i)).index_mul_card
  rw [hc, card_autP] at h
  omega

theorem innerP_normal (i : Fin 2) :
    ((innerP i).subgroupOf (AutMathieuTwelve.autP i)).Normal :=
  Subgroup.normal_of_index_eq_two (innerP_index i)

/-- The original inner endpoint and full outer Borel generate the outer endpoint. -/
theorem autP_eq_innerP_sup_autB (i : Fin 2) :
    AutMathieuTwelve.autP i = innerP i ⊔ AutMathieuTwelve.autB := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
    (sup_le (innerP_le_autP i) (Subgroup.map_mono le_sup_right))
  have h192 := Subgroup.card_dvd_of_le
    (show innerP i ≤ innerP i ⊔ AutMathieuTwelve.autB from le_sup_left)
  have h128 := Subgroup.card_dvd_of_le
    (show AutMathieuTwelve.autB ≤ innerP i ⊔ AutMathieuTwelve.autB from le_sup_right)
  rw [card_innerP] at h192
  rw [card_autB] at h128
  have hd := Nat.lcm_dvd h192 h128
  norm_num at hd
  rw [card_autP]
  exact Nat.le_of_dvd Nat.card_pos hd

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase.ModelProducts
