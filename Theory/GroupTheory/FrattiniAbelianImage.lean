module

public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Abelian images detected above a normal prime subgroup

If the quotient above the pulled-back Frattini subgroup has prime-group
abelianization, every commutative image is a prime group. A Sylow subgroup
and the derived subgroup generate the Frattini quotient; nongeneration
lifts generation to the original group. This supplies the abelian-action
step used in Aschbacher--Smith 15.3.37.
-/

public section
open Subgroup
open scoped commutatorElement

namespace MonoidHom
variable {G Q A : Type*} [Group G] [Group Q] [Group A] [Finite G]
    {p : ℕ} [Fact p.Prime]

theorem isPGroup_range_of_frattini_shadow
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = (frattini (G ⧸ N)).comap (QuotientGroup.mk' N))
    (hab : IsPGroup p (Q ⧸ commutator Q))
    [IsMulCommutative A] (f : G →* A) : IsPGroup p f.range := by
  let : Finite Q := Finite.of_surjective q hq
  let P : Sylow p G := Sylow.nonempty.some
  let D : Subgroup G := commutator G ⊔ (P : Subgroup G)
  have hcomm : (commutator G).map q = commutator Q := by
    rw [map_commutator_eq, q.range_eq_top.mpr hq, ← _root_.commutator_def]
  have hDq : D.map q = ⊤ := by
    dsimp [D]
    rw [Subgroup.map_sup, hcomm, sup_comm]
    exact (P.mapSurjective hq).sup_eq_top_of_quotient_isPGroup (commutator Q) hab
  have hgen : D ⊔ q.ker = ⊤ := by
    have h := congrArg (Subgroup.comap q) hDq
    simpa only [comap_map_eq, comap_top] using h
  let r := QuotientGroup.mk' N
  have hphi : q.ker.map r = frattini (G ⧸ N) := by
    rw [hker]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  have hDmod : D.map r = ⊤ := by
    apply frattini_nongenerating
    have h := congrArg (Subgroup.map r) hgen
    have hr : (⊤ : Subgroup G).map r = ⊤ :=
      map_top_of_surjective r (QuotientGroup.mk'_surjective N)
    simpa only [Subgroup.map_sup, hphi, hr] using h
  have hD : D = ⊤ := by
    have h := congrArg (Subgroup.comap r) hDmod
    have hND : N ≤ D := (hN.le_sylow_of_normal P).trans le_sup_right
    simpa only [comap_map_eq, r, QuotientGroup.ker_mk', sup_of_le_left hND,
      comap_top] using h
  have hc : commutator G ≤ f.ker := by
    rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  have hcmap : (commutator G).map f = ⊥ := by
    exact le_bot_iff.mp ((map_mono hc).trans_eq (map_ker_self f))
  have hPf : (P : Subgroup G).map f = f.range := by
    have h := congrArg (Subgroup.map f) hD
    simpa only [D, Subgroup.map_sup, hcmap, bot_sup_eq, ← MonoidHom.range_eq_map] using h
  exact hPf ▸ P.isPGroup'.map f
end MonoidHom
