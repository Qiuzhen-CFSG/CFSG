module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.PCoreLocalSetup


/-!
# Full support of an odd supplement on the two-core

If X=O₂(X)Y is two-perfect and Y has odd order, then [O₂(X),Y]=O₂(X).
Indeed D=[O₂(X),Y] is normal in X, and DY is normal with a two-group
quotient. Two-perfectness forces DY=X; intersect with O₂(X) and use the
coprime orders to obtain D=O₂(X). An embedded version retains the actual
ambient subgroups and maps.

This supplies full support for the component-invariant section of
O₂(Ξ_p(K_U))U/U in Aschbacher–Smith, Lemma 8.2.7, printed p.718.
-/

public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An odd supplement in a two-perfect group acts fully on the two-core. -/
theorem commutator_two_core_eq_of_odd_supplement (Y : Subgroup G)
    (hperfect : IsPPerfect 2 G) (hY : Odd (Nat.card Y))
    (hgen : pCore 2 G ⊔ Y = ⊤) : ⁅pCore 2 G, Y⁆ = pCore 2 G := by
  let Q := pCore 2 G
  let D := ⁅Q, Y⁆
  have hDQ : D ≤ Q := commutator_le_left Q Y
  let _ : D.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le (normalizer_commutator_ge_left Q Y) (normalizer_commutator_ge_right Q Y)))
  let Z := Y ⊔ D
  have hQZ : Q ≤ normalizer (Z : Set G) :=
    le_normalizer_sup_of_commutator_le Y Q Y D le_rfl (by rw [commutator_comm])
  let _ : Z.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le hQZ ((show Y ≤ Z from le_sup_left).trans Z.le_normalizer)))
  have hZQ : Z ⊔ Q = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hquot := isPGroup_quotient_of_sup_eq_top Z Q pCore_isPGroup hZQ
  have hZtop : Z = ⊤ := by
    have hres : pResidual 2 G ≤ Z := (pResidual_le_iff_isPGroup_quotient 2 Z).mpr hquot
    rw [(pResidual_eq_top_iff 2 G).mpr hperfect] at hres
    exact top_unique hres
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card Y) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact hY.coprime_two_left.pow_left n
  have hdis : Disjoint Q Y := disjoint_of_coprime_natCard hcop
  apply le_antisymm hDQ
  intro q hq
  have hqZ : q ∈ Z := hZtop ▸ mem_top q
  obtain ⟨y, hy, d, hd, rfl⟩ := mem_sup_of_normal_right.mp hqZ
  have hyQ : y ∈ Q := by simpa using Q.mul_mem hq (Q.inv_mem (hDQ hd))
  have hy1 : y = 1 := disjoint_def.mp hdis hyQ hy
  simpa only [hy1, one_mul] using hd

/-- The preceding identity in an arbitrary ambient group. -/
theorem embedded_commutator_two_core_eq_of_odd_supplement (X Y : Subgroup G)
    (hYX : Y ≤ X) (hperfect : IsPPerfect 2 X) (hY : Odd (Nat.card Y))
    (hgen : X.pCoreIn 2 ⊔ Y = X) : ⁅X.pCoreIn 2, Y⁆ = X.pCoreIn 2 := by
  have hgen' : pCore 2 X ⊔ Y.subgroupOf X = ⊤ := by
    apply map_injective X.subtype_injective
    rw [map_sup, map_subgroupOf_eq_of_le hYX, ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hodd : Odd (Nat.card (Y.subgroupOf X)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hYX).toEquiv]
  have h := congrArg (map X.subtype)
    (commutator_two_core_eq_of_odd_supplement (Y.subgroupOf X) hperfect hodd hgen')
  simpa only [map_commutator, map_subgroupOf_eq_of_le hYX, pCoreIn] using h
end Subgroup
