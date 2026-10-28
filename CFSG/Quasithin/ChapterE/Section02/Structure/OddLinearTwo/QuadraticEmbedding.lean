module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.QuadraticInnerField
public import GorensteinWalter.PGammaL2NormalExtension

/-!
# The faithful original quadratic semilinear action

Trivial two-core and the centerless normal component make its original
conjugation action faithful. The actual automorphism theorem transports
it into the projective semilinear group, retaining the given component
map. The proved source exclusion of inner-field actions supplies a
non-inner linear coordinate in this same image.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
 theorem quadratic_linear_source_semilinear_embedding
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2 F) :
    ∃ q : H →* PGammaL2 F, Function.Injective q ∧
      (∀ k : K, q k = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (eK k))) ∧
      pGammaL2PSLRange F ≤ q.range ∧
      ∃ y ∈ q.range, y.left ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have hlarge : 3 < Nat.card F := by rw [hF]; nlinarith
  let eA := pGammaL2EquivMulAutPSL2 F hodd hlarge
    (pGammaL2ToMulAutPSL2_surjective F hF hodd hlarge)
  let q : H →* PGammaL2 F := eA.symm.toMonoidHom.comp
    ((MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal : H →* MulAut K))
  have hZ : center K = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have hh : eK k ∈ center (PSL2 F) := (centerCongr eK ⟨k, hk⟩).property
    rw [psl2_center_eq_bot F, mem_bot] at hh
    exact mem_bot.mpr (eK.injective (by simpa only [map_one] using hh))
  have hq : Function.Injective q := eA.symm.injective.comp
    ((MulAut.congr eK).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot K
      (centralizer_eq_bot_of_centerless_sylow_supplement T K hgen hZ hO)))
  have hback (a : H) : pGammaL2ToMulAutPSL2 F hodd hlarge (q a) =
      MulAut.congr eK (MulAut.conjNormal a) := eA.apply_symm_apply _
  have hqK (k : K) : q k = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (eK k)) := by
    apply pGammaL2ToMulAutPSL2_injective F hodd hlarge
    rw [hback, MulAut.conjNormal_val, MulAut.congr_conj,
      pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
  refine ⟨q, hq, hqK, ?_, ?_⟩
  · rintro x ⟨a, rfl⟩
    exact ⟨eK.symm a, by rw [hqK, eK.apply_symm_apply]; rfl⟩
  · obtain ⟨a, ha⟩ := quadratic_linear_not_inner_field T hP K hgen hO ho hF hp eK
    refine ⟨q a, ⟨a, rfl⟩, ?_⟩
    rintro ⟨g, hg⟩
    apply ha
    refine ⟨g, (q a).right, ?_⟩
    rw [← hback]
    nth_rw 1 [← SemidirectProduct.inl_left_mul_inr_right (q a)]
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr,
      ← hg, pgl2InnerAutPSL2_toPGL]
end CFSG.Quasithin.ChapterE.Structure
