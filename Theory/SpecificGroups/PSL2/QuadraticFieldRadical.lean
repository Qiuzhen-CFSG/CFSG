module
public import Theory.SpecificGroups.PSL2.OddSylowFixers
public import Theory.SpecificGroups.PSL2.OddSquareFieldFixed
public import Theory.GroupTheory.AutomorphismOvergroupRadical
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# The radical of an odd quadratic-field involution centralizer

The coefficient involution on PSL2(p²) fixes the actual PGL2(p).
For p greater than three, PGL2(p) embeds in Aut(PSL2(p)) over the
centerless simple inner subgroup, so its solvable radical is trivial.
This is the field-automorphism branch of the original rank-one inspection
in Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem pgl_radical_bot {E : Type*} [Field E] [Finite E]
    (hE : IsOddPrimePower (Nat.card E)) (hl : 3 < Nat.card E) :
    solvableRadical (GorensteinWalter.PGL2 E) = ⊥ := by
  let : Finite (GorensteinWalter.PGL2 E) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let : IsSimpleGroup PSL(2,E) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Group.IsPerfect PSL(2,E) := psl2_isPerfect_of_card_gt_three E hl
  let f := pgl2InnerAutPSL2 E hE hl
  let e := MonoidHom.ofInjective (pgl2InnerAutPSL2_injective E hE hl)
  have hi : MulAut.innerSubgroup PSL(2,E) ≤ f.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL x,pgl2InnerAutPSL2_toPGL E hE hl x⟩
  have hb := MulAut.radical_free_of_inner_le (psl2_center_eq_bot E) f.range hi
  have he := map_solvableRadical_equiv e
  rw [hb] at he
  exact ((solvableRadical (GorensteinWalter.PGL2 E)).map_eq_bot_iff_of_injective e.injective).mp he

/-- The full fixed group of a quadratic odd-field coefficient involution
has trivial radical when its fixed field has more than three elements. -/
theorem quadratic_field_involution_radical_bot {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p^2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    solvableRadical (psl2FieldAut F σ).fixedSubgroup = ⊥ := by
  let E := FixedPoints.subfield (zpowers σ) F
  let : Finite (GorensteinWalter.PGL2 E) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  have hE : Nat.card E = p := OddSquareFieldFixed.fixed_subfield_card hF σ hσ
  obtain ⟨e⟩ := OddSquareFieldFixed.coefficient_fixed_equiv ho hF σ hσ
  have hb := pgl_radical_bot (E := E) ⟨p,1,hp,ho,by decide,by simpa using hE⟩ (by omega)
  have he := map_solvableRadical_equiv e
  rw [hb] at he
  exact ((solvableRadical (psl2FieldAut F σ).fixedSubgroup).map_eq_bot_iff_of_injective e.injective).mp he
end Theory.PSL2
