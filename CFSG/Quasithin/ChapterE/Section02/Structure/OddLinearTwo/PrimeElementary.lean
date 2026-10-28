module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeSylow
public import Theory.GroupTheory.SpecificGroups.LargeDihedralElementary
public import Theory.ElementaryAbelian.Basic

/-!
# The literal elementary-normal exclusion in the prime odd row

The source hypotheses identify the original Sylow subgroup as a dihedral
two-group of order at least sixteen. Every elementary subgroup normal in
that Sylow has order at most two. Thus a noncyclic elementary subgroup from
the original E.2.7 setup excludes this odd prime-field branch directly;
no recognition of V or containment in a replacement two-core is assumed.

Source: Aschbacher–Smith E.2.7, printed pp.220–221, using E.2.2(2c).
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure

/-- The original normal elementary subgroup in the prime odd row is at most cyclic. -/
theorem prime_linear_source_elementary_card_le_two
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    Nat.card V ≤ 2 := by
  obtain ⟨m, hm, ⟨e⟩⟩ := prime_linear_source_sylow_dihedral T hP K hgen hO ho hF hp eK
  let := hV
  let W := V.subgroupOf (T : Subgroup H)
  let : W.Normal := (normal_subgroupOf_iff_le_normalizer hVT).mpr hVN
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVT
  let D := W.map e.toMonoidHom
  let : D.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.toMonoidHom
  have hD := DihedralGroup.elementary_normal_card_le_two_of_large hm D
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 D))
  rw [card_map_of_injective e.injective] at hD
  rwa [Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv] at hD

/-- The actual noncyclic elementary E.2.7 setup rules out the prime odd row. -/
theorem prime_linear_source_not_elementary_four
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcard : 4 ≤ Nat.card V) : False := by
  have hh := prime_linear_source_elementary_card_le_two T hP K hgen hO ho hF hp eK V hV hVT hVN
  omega

end CFSG.Quasithin.ChapterE.Structure
