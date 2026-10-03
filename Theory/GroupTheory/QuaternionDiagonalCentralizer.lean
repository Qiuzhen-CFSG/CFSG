module
public import Theory.GroupTheory.QuaternionCentralProductDiagonal
public import Theory.GroupTheory.QuaternionCentralProductCenter

/-!
# Self-centralization of a quaternion diagonal

Every diagonal elementary eight in a quaternion central product is
self-centralizing inside that central product. The statement uses the actual
diagonal defined from the given factor isomorphism and makes no assertion
about its centralizer outside the central product.

The diagonal D joined with either quaternion factor C generates the whole
central product. Write a centralizing element as d*c. Since D is elementary,
the C component still centralizes D. Cancelling the other factor from the
matching generators b*θ(b) shows that c centralizes C. The proved factor-center
identification places c in the shared intersection, which lies in D. Thus the
original element lies in D; the reverse inclusion follows from commutativity.

This supplies the intrinsic centralizer input to the terminal normalizer
calculation for the selected elementary eight in Stellmacher (9.1), Journal
of Algebra190 (1997), p.48. Selection and the ambient centralizer transfer
remain separate results.
-/

open scoped Pointwise
namespace Subgroup

/-- A diagonal elementary eight is self-centralizing within its quaternion
central product. -/
public theorem inf_centralizer_quaternionDiagonal
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (model : B ≃* QuaternionGroup 2) (θ : B ≃* C)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) :
    (B ⊔ C) ⊓ centralizer (quaternionDiagonal B C θ hcomm : Set G) =
      quaternionDiagonal B C θ hcomm := by
  have hcenterC : B ⊓ C = (center C).map C.subtype := by
    rw [inf_comm]
    exact intersection_eq_factor_center C B ⟨θ.symm.trans model⟩
      (by simpa only [inf_comm] using hinter)
      (fun c hc b hb => (hcomm b hb c hc).symm)
  let D := quaternionDiagonal B C θ hcomm
  obtain ⟨hElem,_,hID,hDV⟩ := quaternion_diagonal_elementary_eight B C model θ hinter hcomm
  let := hElem
  have hDC : D ≤ centralizer (D : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hdiag (a : B) : (a:G)*(θ a:G) ∈ D :=
    (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left) ⟨a,rfl⟩
  have hBCn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro a ha c hc
    exact (hcomm a ha c hc).symm
  have hDn : D ≤ normalizer (C : Set G) := hDV.trans (sup_le hBCn C.le_normalizer)
  have hsup : D ⊔ C = B ⊔ C := by
    apply le_antisymm (sup_le hDV le_sup_right)
    apply sup_le ?_ le_sup_right
    intro a ha
    have hh := (D ⊔ C).mul_mem (mem_sup_left (hdiag ⟨a,ha⟩))
      (mem_sup_right (C.inv_mem (θ ⟨a,ha⟩).property))
    simpa only [mul_inv_cancel_right] using hh
  apply le_antisymm ?_ (le_inf hDV hDC)
  intro x hx
  have hxprod : x ∈ (D : Set G)*(C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right D C hDn, hsup]
    exact hx.1
  obtain ⟨d,hd,c,hc,hxprod⟩ := hxprod
  change d*c=x at hxprod
  have hcfix : c ∈ centralizer (D : Set G) := by
    have hh := (centralizer (D : Set G)).mul_mem
      ((centralizer (D : Set G)).inv_mem (hDC hd)) hx.2
    rw [← hxprod] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hcz : (⟨c,hc⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a,ha⟩ := θ.surjective y
    have hh := mem_centralizer_iff.mp hcfix ((a:G)*(θ a:G)) (hdiag a)
    change ((a:G)*(θ a:G))*c = c*((a:G)*(θ a:G)) at hh
    rw [← ha]
    apply Subtype.ext
    apply mul_left_cancel (a := (a:G))
    calc
      (a:G)*((θ a:G)*c) = ((a:G)*(θ a:G))*c := (mul_assoc _ _ _).symm
      _ = c*((a:G)*(θ a:G)) := hh
      _ = (a:G)*(c*(θ a:G)) := by rw [← mul_assoc, ← hcomm a a.property c hc, mul_assoc]
  have hcI : c ∈ B ⊓ C := hcenterC.symm ▸ (show c ∈ (center C).map C.subtype from ⟨⟨c,hc⟩,hcz,rfl⟩)
  rw [← hxprod]
  exact D.mul_mem hd (hID hcI)
end Subgroup
