module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.Numerics
public import Theory.SpecificGroups.SymmetricFive.ThreeCentralizer

/-!
# The cubic centralizer quotient has order at most sixteen

The source cubic subgroup has order three and embeds under the actual Ru2
map H → S₅. Its centralizer therefore maps into a subgroup of order six,
with kernel the quaternion group C_Q(B). Dividing by the literal central
subgroup B gives the bound sixteen. The subsequent quaternion generators
saturate this bound; no centralizer order or splitting is assumed here.

Source: Aschbacher–Smith J.2.5, printed p.434 of `refs/quasithin.pdf`.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- The original cubic subgroup is contained in its H-centralizer. -/
theorem cubic_le_CB (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    BSubgroup d.toTypeRuSetup B ≤ CB d.toTypeRuSetup B := by
  let A := BSubgroup d.toTypeRuSetup B
  have hA : Nat.card A = 3 := SpecialCore.cubicSubgroup_card d.toTypeRuSetup B
    d.card_Z (d.center_eq.le.trans inf_le_left)
  let : IsCyclic A := isCyclic_of_prime_card hA
  refine le_inf ((SpecialCore.cubicSubgroup_le_K d.toTypeRuSetup B).trans
    d.toTypeRuSetup.K_le_H) ?_
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : A) ⟨a, ha⟩)

/-- The actual quotient C_H(B)/B has order at most sixteen. -/
theorem cubic_quotient_card_le (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (cp : CentralProductData d.toTypeRuSetup B) :
    Nat.card (CB d.toTypeRuSetup B ⧸
      (BSubgroup d.toTypeRuSetup B).subgroupOf (CB d.toTypeRuSetup B)) ≤ 16 := by
  let D := d.toTypeRuSetup
  let A := BSubgroup D B
  let C := CB D B
  have hAH : A ≤ D.H := (cubic_le_CB d B).trans inf_le_left
  have hAC : A ≤ C := cubic_le_CB d B
  have hA : Nat.card A = 3 := SpecialCore.cubicSubgroup_card D B
    d.card_Z (d.center_eq.le.trans inf_le_left)
  let f : C →* S5 := D.ru2.quotientMap.comp (inclusion inf_le_left)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA])
  let t := D.ru2.quotientMap (inclusion hAH b)
  have ht : orderOf t = 3 := (orderOf_injective _ (SpecialCore.cubic_ru2_injective D B) b).trans hb
  have hrange : f.range ≤ centralizer ({t} : Set S5) := by
    rintro _ ⟨c, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change D.ru2.quotientMap (inclusion inf_le_left c) *
      D.ru2.quotientMap (inclusion hAH b) =
      D.ru2.quotientMap (inclusion hAH b) * D.ru2.quotientMap (inclusion inf_le_left c)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (c.property.2 b b.property).symm
  have hr : Nat.card f.range ≤ 6 := by
    have h := card_le_of_le hrange
    rwa [Theory.SpecificGroups.SymmetricFive.centralizer_three_card t ht] at h
  have hHC : HB D B ≤ C := inf_le_inf D.ru2.six.section_le le_rfl
  have hk : f.ker = (HB D B).subgroupOf C := by
    ext c
    change D.ru2.quotientMap ⟨(c : G), c.property.1⟩ = 1 ↔
      (c : G) ∈ D.Q ⊓ centralizer (A : Set G)
    rw [← MonoidHom.mem_ker, D.ru2.quotient_kernel]
    exact ⟨fun h => ⟨h, c.property.2⟩, fun h => h.1⟩
  have hkcard : Nat.card f.ker = 8 := by
    obtain ⟨e⟩ := cp.quaternion
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hHC).toEquiv,
      Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hkcard] at hc
  have hCcard : Nat.card C ≤ 48 := by omega
  have hquot := card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, hA] at hquot
  change Nat.card (C ⧸ A.subgroupOf C) ≤ 16
  omega
end CFSG.Quasithin.ChapterJ.Fusion.Outer
