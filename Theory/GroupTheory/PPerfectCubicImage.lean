module

public import Theory.GroupTheory.PPerfectHom
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Index

/-!
# Nontrivial images of two-perfect groups with cubic core quotient

A surjective image has core quotient of order dividing three. If that
quotient collapsed, the whole image would be a two-group, contrary to
two-perfectness of the original group and nontriviality of the map.

Source application: Aschbacher--Smith12.7.15(4), printed p.843.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- A nontrivial quotient retains the cubic quotient by its own two-core. -/
theorem cubic_core_quotient_of_twoPerfect_image
    (hG : IsPPerfect 2 G) (hc : Nat.card (G ⧸ pCore 2 G) = 3)
    (f : G →* H) (hf : Function.Surjective f) (hne : f ≠ 1) :
    Nat.card (H ⧸ pCore 2 H) = 3 := by
  have hm : (pCore 2 G).map f ≤ pCore 2 H :=
    le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  let q := (QuotientGroup.mk' (pCore 2 H)).comp f
  have hk : pCore 2 G ≤ q.ker := by
    rw [show q = (QuotientGroup.mk' (pCore 2 H)).comp f from rfl,
      ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact map_le_iff_le_comap.mp hm
  let g : (G ⧸ pCore 2 G) →* (H ⧸ pCore 2 H) :=
    QuotientGroup.lift (pCore 2 G) q hk
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y,rfl⟩ := (QuotientGroup.mk'_surjective (pCore 2 H)).comp hf x
    exact ⟨QuotientGroup.mk' (pCore 2 G) y,rfl⟩
  have hd : Nat.card (H ⧸ pCore 2 H) ∣ 3 := hc ▸ card_dvd_of_surjective g hg
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hone | hthree
  · have he : pCore 2 H = ⊤ := index_eq_one.mp hone
    have hp : IsPGroup 2 H := pCore_isPGroup.of_equiv
      ((MulEquiv.subgroupCongr he).trans (Subgroup.topEquiv))
    exact (hne (hG.hom_eq_one_of_isPGroup hp f)).elim
  · exact hthree

end Theory.GroupTheory
