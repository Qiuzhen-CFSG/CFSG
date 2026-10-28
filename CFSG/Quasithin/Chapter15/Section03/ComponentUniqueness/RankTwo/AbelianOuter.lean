module

public import Theory.GroupTheory.FrattiniAbelianImage
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Definitions

/-!
# Abelian actions of the actual rank-two shadow

The abelianization of S3 times S3 is a two-group. Pulling this through
the actual O2/Frattini quotient shows that every commutative image of
Yplus joined with S is a two-group, and hence kills two-perfect Yplus.
Both permitted cubic quotients, of orders nine and twenty-seven, remain
allowed. Source: Aschbacher--Smith 15.3.37, printed p.1135.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo

private theorem symmetricThreeProduct_abelianization_isTwoGroup :
    IsPGroup 2 ((Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ⧸
      commutator (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let Q := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)
  let f := QuotientGroup.mk' (commutator Q)
  let : IsMulCommutative (Q ⧸ commutator Q) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) x
  obtain ⟨s, hs⟩ := (by decide : ∀ a : Equiv.Perm (Fin 3),
    ∃ t, t * a * t⁻¹ = a⁻¹) y.1
  obtain ⟨t, ht⟩ := (by decide : ∀ a : Equiv.Perm (Fin 3),
    ∃ t, t * a * t⁻¹ = a⁻¹) y.2
  have hi : (s, t) * y * (s, t)⁻¹ = y⁻¹ := Prod.ext hs ht
  have he : f y = (f y)⁻¹ := by
    calc
      f y = f (s, t) * f y * (f (s, t))⁻¹ := by
        rw [mul_comm' (f (s, t)) (f y), mul_inv_cancel_right]
      _ = f ((s, t) * y * (s, t)⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = f (y⁻¹) := congrArg f hi
      _ = (f y)⁻¹ := map_inv f y
  refine ⟨1, ?_⟩
  change f y ^ (2 ^ 1) = 1
  rw [pow_one, pow_two]
  calc
    f y * f y = (f y)⁻¹ * f y := congrArg (fun a => a * f y) he
    _ = 1 := inv_mul_cancel _

variable {G A : Type*} [Group G] [Finite G] [Group A] [IsMulCommutative A]
    {Yplus S : Subgroup G}

theorem RankTwoShadow.abelian_range_isTwoGroup (h : RankTwoShadow Yplus S)
    (f : (Yplus ⊔ S : Subgroup G) →* A) : IsPGroup 2 f.range := by
  obtain ⟨e⟩ := h
  let H := Yplus ⊔ S
  let q : H →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (twoFrattiniCore H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = twoFrattiniCore H := by
    ext x
    change e (QuotientGroup.mk' (twoFrattiniCore H) x) = 1 ↔ x ∈ twoFrattiniCore H
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  exact MonoidHom.isPGroup_range_of_frattini_shadow (pCore 2 H) pCore_isPGroup
    q hq hker symmetricThreeProduct_abelianization_isTwoGroup f

theorem abelian_action_trivial (h : RankTwoShadow Yplus S)
    (hY : IsPPerfect 2 Yplus) (f : (Yplus ⊔ S : Subgroup G) →* A) (y : Yplus) :
    f (inclusion le_sup_left y) = 1 := by
  have he := hY.hom_eq_one_of_isPGroup (h.abelian_range_isTwoGroup f)
    (f.rangeRestrict.comp (inclusion le_sup_left))
  exact congrArg (fun a : Yplus →* f.range => (a y : A)) he

end CFSG.Quasithin.Chapter15.Section03.RankTwo
