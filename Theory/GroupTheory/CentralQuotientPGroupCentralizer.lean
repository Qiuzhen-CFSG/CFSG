module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Central p-kernels and element centralizers

For the inverse image of an element centralizer in a central quotient,
commutation with the chosen lift defines a homomorphism into the central
kernel. Its kernel embeds in the original element centralizer. If both
are p-groups, the inverse image and its quotient image are p-groups.

The source consumer applies this to `C_G(z)/⟨z⟩` and the original marked
involution `t`, preserving the actual quotient map. Source: Aschbacher--Smith,
Lemma 13.9.8, printed p.972, first paragraph.
-/

public section
namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] {p : ℕ}

/-- A central p-kernel preserves the p-group property of an element
centralizer. The enlarged preimage centralizer is controlled by its actual
central commutator homomorphism. -/
theorem isPGroup_centralizer_quotient_of_central_kernel
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G) (hNp : IsPGroup p N)
    (t : G) (hC : IsPGroup p (centralizer ({t} : Set G))) :
    IsPGroup p (centralizer ({QuotientGroup.mk' N t} : Set (G ⧸ N))) := by
  let π := QuotientGroup.mk' N
  let D := centralizer ({π t} : Set (G ⧸ N))
  let H := D.comap π
  have hmem (x : H) : ⁅(x : G),t⁆ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π ⁅(x : G),t⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_singleton_iff.mp x.property
  let f : H →* N :=
    { toFun := fun x => ⟨⁅(x : G),t⁆,hmem x⟩
      map_one' := Subtype.ext (commutatorElement_one_left t)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅(a : G)*(b : G),t⁆ = ⁅(a : G),t⁆ * ⁅(b : G),t⁆
        have hc := mem_center_iff.mp (hN (hmem b)) (a : G)
        have hs := mem_center_iff.mp (hN (hmem a)) ⁅(b : G),t⁆
        rw [commutatorElement_mul_left_eq_conj_mul,hc]
        simpa only [mul_assoc,mul_inv_cancel_left] using hs) }
  let j : f.ker →* centralizer ({t} : Set G) :=
    { toFun := fun x => ⟨x.val.val,mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val x.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : centralizer ({t} : Set G) => (z : G)) hxy
  have hk : IsPGroup p f.ker := hC.of_injective j hj
  have hHp : IsPGroup p H := by
    have hh := (hNp.to_subgroup ⊤).comap_of_ker_isPGroup f hk
    rw [comap_top] at hh
    exact hh.of_surjective (Subgroup.topEquiv (G := H)).toMonoidHom
      (Subgroup.topEquiv (G := H)).surjective
  let q : H →* D :=
    { toFun := fun x => ⟨π x,x.property⟩
      map_one' := Subtype.ext (π.map_one)
      map_mul' := fun x y => Subtype.ext (π.map_mul x y) }
  apply hHp.of_surjective q
  intro y
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective N y.val
  have hxH : x ∈ H := by
    change π x ∈ D
    exact hx.symm ▸ y.property
  exact ⟨⟨x,hxH⟩,Subtype.ext hx⟩
end Subgroup
