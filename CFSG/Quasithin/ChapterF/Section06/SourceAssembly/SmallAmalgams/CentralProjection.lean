module

public import CFSG.Quasithin.ChapterF.Section06.Basic
import Mathlib.Tactic

/-!
# Faithful local projection through an odd ambient center

Each Goldschmidt vertex has center contained in its two-core, because its
quotient by that core is centerless S₃. An odd ambient center therefore
intersects either vertex trivially. This keeps the literal central quotient
map faithful on both original vertices.

Source: the central-cover cases of Aschbacher--Smith F.6.18, printed p.310.
-/

public section
open Subgroup Equiv
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem symmetricThree_central_eq_one (x : Perm (Fin 3))
    (hx : ∀ y, y * x = x * y) : x = 1 := by
  decide +revert +kernel

/-- The center of a Goldschmidt vertex lies in its actual two-core. -/
theorem IsGoldschmidtTriple.left_center_le_twoCore
    (h : IsGoldschmidtTriple G₁ G₂) : center G₁ ≤ pCore 2 G₁ := by
  intro x hx
  obtain ⟨e⟩ := h.quotient_left
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₁))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfx : f x = 1 := symmetricThree_central_eq_one _ (by
    intro y
    obtain ⟨z, rfl⟩ := hf y
    rw [← map_mul, ← map_mul]
    exact congrArg f ((mem_center_iff.mp hx) z))
  apply (QuotientGroup.eq_one_iff x).mp
  exact e.injective (hfx.trans (map_one e).symm)

/-- An odd ambient center gives an injective literal central projection on
an original Goldschmidt vertex; no choice of quotient coordinates is needed. -/
theorem IsGoldschmidtTriple.left_center_quotient_injective
    (h : IsGoldschmidtTriple G₁ G₂) (hZ : Odd (Nat.card (center G))) :
    Function.Injective ((QuotientGroup.mk' (center G)).comp G₁.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hglobal : (x : G) ∈ center G := (QuotientGroup.eq_one_iff (x : G)).mp hx
  have hlocal : x ∈ center G₁ := mem_center_iff.mpr
    (fun y => Subtype.ext ((mem_center_iff.mp hglobal) y))
  let y : pCore 2 G₁ := ⟨x, h.left_center_le_twoCore hlocal⟩
  let z : center G := ⟨x, hglobal⟩
  have heq : orderOf z = orderOf y := (Subgroup.orderOf_coe z).symm.trans
    ((Subgroup.orderOf_coe x).trans (Subgroup.orderOf_coe y))
  have hcop : Nat.Coprime (orderOf z) (Nat.card (center G)) := by
    rw [heq]
    exact pCore_isPGroup.orderOf_coprime hZ.coprime_two_left y
  have hz : z = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_natCard z))
  exact Subtype.ext (congrArg (center G).subtype hz)

end CFSG.Quasithin.ChapterF
