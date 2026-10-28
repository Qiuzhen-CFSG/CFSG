module

public import Theory.GroupAction.ClassTwoCoprimeFixedCenter
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The original center in a coprime relative centralizer

Apply the class-two fixed-center theorem to the literal conjugation action
on a normalized subgroup. Both centers are returned in the original ambient
group, retaining their actual elements and inclusions.
-/

public section
open Subgroup
namespace Theory.GroupAction

/-- Coprime centralization in a class-two subgroup retains its whole center. -/
theorem centerIn_centralizer_eq_of_class_two_coprime
    {G : Type*} [Group G] [Finite G] (Q A : Subgroup G)
    (hn : A ≤ normalizer (Q : Set G))
    (hs : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card A) (Nat.card Q))
    (hclass : _root_.commutator Q ≤ center Q)
    (hz : centerIn Q ≤ centralizer (A : Set G)) :
    centerIn (Q ⊓ centralizer (A : Set G) : Subgroup G) = centerIn Q := by
  let native := conjMulDistribMulActionOfLeNormalizer A Q hn
  let _ : MulDistribMulAction A Q := native
  let _ : SMul A Q := native.toSMul
  let _ : MulAction A Q := native.toMulAction
  let F := fixedPointSubgroup A Q
  have hfix (a : A) (z : center Q) : a • (z:Q)=z := by
    have hzQ : ((z:Q):G) ∈ centerIn Q := by
      rw [centerIn_eq_map_center]
      exact mem_map_of_mem Q.subtype z.property
    apply Subtype.ext
    change (a:G)*(z:Q)*(a:G)⁻¹=(z:Q)
    rw [mem_centralizer_iff.mp (hz hzQ) a a.property,mul_inv_cancel_right]
  have hc := center_fixed_eq_of_class_two_coprime hs hcop hclass hfix
  have hfixed (q : Q) : q ∈ F ↔ (q:G) ∈ centralizer (A : Set G) := by
    constructor
    · intro hq
      apply mem_centralizer_iff.mpr
      intro a ha
      have hh := congrArg Subtype.val (hq ⟨a,ha⟩)
      change a*(q:G)*a⁻¹=(q:G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hq a
      apply Subtype.ext
      change (a:G)*(q:G)*(a:G)⁻¹=(q:G)
      rw [mem_centralizer_iff.mp hq a a.property,mul_inv_cancel_right]
  ext x
  constructor
  · intro hx
    let q : Q := ⟨x,hx.1.1⟩
    have hq : q ∈ F := (hfixed q).mpr hx.1.2
    have hqcenter : (⟨q,hq⟩ : F) ∈ center F := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply Subtype.ext
      exact mem_centralizer_iff.mp hx.2 y.val.val ⟨y.val.property,(hfixed y.val).mp y.property⟩
    have hqZ : q ∈ center Q := hc.le hqcenter
    rw [centerIn_eq_map_center]
    exact mem_map_of_mem Q.subtype hqZ
  · intro hx
    refine ⟨⟨hx.1,hz hx⟩,?_⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    exact mem_centralizer_iff.mp hx.2 y hy.1

end Theory.GroupAction
