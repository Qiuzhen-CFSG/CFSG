module
public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.SpecificGroups.SL2.OddCoreAndRank

/-!
# Central elementary subgroups and the generation parameter

If every elementary abelian two-subgroup is central, every weak closure is
normal. Its normalizer already generates the whole group, so E-generation
holds at level one. In odd-characteristic SL₂ every involution is scalar;
the central involution then makes the generation parameter exactly one.

This calculation uses the original group in Definitions E.1.5–E.1.6 of
Aschbacher–Smith, printed p.210. It does not pass to a two-core quotient.
The field-five application is used to audit the numerical sentence of E.2.2.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE

theorem isEGenerated_one_of_elementary_le_center {G : Type*} [Group G] [Finite G]
    (hc : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ center G) :
    IsEGenerated 1 G := by
  intro T Ω hΩ
  have hW : weakClosure (T : Subgroup G) Ω ≤ center G := by
    apply sSup_le
    intro A hA
    exact hc A (hΩ.1 A hA.1)
  let : (weakClosure (T : Subgroup G) Ω).Normal := ⟨by
    intro x hx g
    have he : g*x*g⁻¹=x := by
      rw [(mem_center_iff.mp (hW hx)) g, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [he] using hx⟩
  change _ ⊔ normalizer (weakClosure (T : Subgroup G) Ω : Set G) = ⊤
  rw [normalizer_eq_top, sup_top_eq]

theorem generationParameter_sl2_odd {F : Type*} [Field F] [Finite F]
    (hF : (2 : F) ≠ 0) : generationParameter SL(2,F) = 1 := by
  have hgen : IsEGenerated 1 SL(2,F) := by
    apply isEGenerated_one_of_elementary_le_center
    intro A hA x hx
    have hs : x ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p (⟨x,hx⟩ : A))
    have hd : (SpecialLinearGroup.toGL x).det = 1 := by apply Units.ext; exact x.property
    rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (SpecialLinearGroup.toGL x) (by rw [← map_pow, hs, map_one]) hd with he | he
    · have hx1 : x=1 := SpecialLinearGroup.toGL_injective (by simpa using he)
      simp only [hx1, one_mem]
    · have hx1 : x = -1 := Subtype.ext (congrArg Units.val he)
      rw [hx1, mem_center_iff]
      intro a
      simp
  have heven : ¬ Odd (Nat.card SL(2,F)) := by
    intro ho
    have hd := orderOf_dvd_natCard (-1 : SL(2,F))
    rw [SpecialLinearGroup.orderOf_neg_one_eq_two hF] at hd
    exact ho.not_two_dvd_nat hd
  have hp := (generationParameter_spec heven ⟨1, by decide, hgen⟩).1
  have hu := generationParameter_le (by decide : 0 < 1) hgen
  omega


end CFSG.Quasithin.ChapterE
