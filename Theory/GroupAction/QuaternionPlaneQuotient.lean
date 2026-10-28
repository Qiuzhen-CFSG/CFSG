module
public import Theory.GroupAction.QuaternionPrimePlane
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreImage
/-!
# Quaternion irreducibility preserves the odd plane through a normal quotient

Let P/O₂(P) be an elementary odd-prime plane, with a faithful quaternion
subgroup in its actual ambient conjugation image. A normal ambient
quotient killing O₂(P) either kills P or preserves this whole plane.
Its kernel is invariant under the actual quaternion action, so the
prime-plane irreducibility theorem proves injectivity in the nontrivial
case. The returned equivalence retains the original quotient formula.

This is the survival step on R₂(PT) in Aschbacher--Smith 13.3.14(d), p.892.
-/

public section
open Subgroup
namespace QuaternionGroup
variable {G : Type*} [Group G] [Finite G]

theorem quotient_core_image_injective
    (P C : Subgroup G) [P.Normal] [C.Normal]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    [IsElementaryAbelian p (P ⧸ pCore 2 P)]
    (hcard : Nat.card (P ⧸ pCore 2 P) = p ^ 2)
    (hk : pCore 2 P ≤ C.comap P.subtype)
    (hne : P.map (QuotientGroup.mk' C) ≠ ⊥)
    (a : QuaternionGroup 2 →* MulAut (P ⧸ pCore 2 P)) (ha : Function.Injective a)
    (hactor : a.range ≤ ((quotientAut (pCore 2 P)).comp
      (MulAut.conjNormal : G →* MulAut P)).range) :
    ∃ e : (P ⧸ pCore 2 P) ≃* P.map (QuotientGroup.mk' C),
      ∀ x : P, (e (QuotientGroup.mk' (pCore 2 P) x) : G ⧸ C) =
        QuotientGroup.mk' C (x : G) := by
  let q := QuotientGroup.mk' C
  let r : P →* P.map q := q.subgroupMap P
  have hr := q.subgroupMap_surjective P
  have hkr : pCore 2 P ≤ r.ker := by
    intro x hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hk hx)
  let f := QuotientGroup.lift (pCore 2 P) r hkr
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ _ hr _
  have hfixed (g : QuaternionGroup 2) (z : P ⧸ pCore 2 P) (hz : z ∈ f.ker) :
      a g z ∈ f.ker := by
    obtain ⟨x,hx⟩ := hactor (show a g ∈ a.range from ⟨g,rfl⟩)
    rw [← hx]
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) z
    change f (quotientAut (pCore 2 P) (MulAut.conjNormal x)
      (QuotientGroup.mk' (pCore 2 P) y)) = 1
    rw [quotientAut_apply_mk]
    apply Subtype.ext
    change q (x * (y : G) * x⁻¹) = 1
    have hqy : q (y : G) = 1 := congrArg Subtype.val hz
    simp only [map_mul,map_inv,hqy,mul_one,mul_inv_cancel]
  have hker : f.ker = ⊥ := by
    rcases faithful_plane_irreducible hp hcard a ha f.ker hfixed with hb | ht
    · exact hb
    · exfalso
      apply hne
      apply le_bot_iff.mp
      rintro z ⟨x,hx,rfl⟩
      have hy : QuotientGroup.mk' (pCore 2 P) (⟨x,hx⟩ : P) ∈ f.ker := ht ▸ mem_top _
      exact congrArg Subtype.val hy
  exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hker,hf⟩,
    fun _ => rfl⟩
end QuaternionGroup
