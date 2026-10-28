module
public import GorensteinWalter.PSL2EvenDefiningKernel
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.GroupTheory.PCoreRestriction

/-!
# The two-core commutator for binary rank-one quotients

If a two-perfect group has quotient PSL₂(q), with q even and at least eight,
its two-core equals its commutator with the group. Modulo that commutator,
the two-core is a central two-group. The quotient is perfect, and the
proved defining-characteristic multiplier bound kills this central kernel.

This supplies the core identification in the odd-degree block branch of
Aschbacher–Smith 5.1.17, printed p.641, using I.1.3 and C.1.13(b)
(refs/quasithin.pdf). No elementary-abelian core hypothesis is needed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
variable {E F : Type*} [_root_.Group E] [Finite E] [Field F] [Finite F]

theorem core_eq_commutator_of_even_psl2
    (hE : IsPPerfect 2 E) (heven : Even (Nat.card F)) (hF : 8 ≤ Nat.card F)
    (e : (E ⧸ pCore 2 E) ≃* PSL(2,F)) :
    pCore 2 E = ⁅pCore 2 E, (⊤ : Subgroup E)⁆ := by
  let U : Subgroup E := ⁅pCore 2 E, ⊤⁆
  have hU : U ≤ pCore 2 E := commutator_le_left _ _
  let q := QuotientGroup.mk' U
  let f : (E ⧸ U) →* PSL(2,F) := e.toMonoidHom.comp
    (QuotientGroup.lift U (QuotientGroup.mk' (pCore 2 E))
      (by simpa only [QuotientGroup.ker_mk'] using hU))
  have hf : Function.Surjective f := e.surjective.comp
    (QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective _) _)
  have hk : f.ker = (pCore 2 E).map q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_lift,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup.map q
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let : Group.IsPerfect (E ⧸ U) :=
    (hE.of_surjective q (QuotientGroup.mk'_surjective U)).isPerfect_of_surjective_pGroup_kernel f hf hp
  have hc : f.ker ≤ center (E ⧸ U) := by
    rw [hk,←commutator_top_right_eq_bot_iff_le_center]
    have ht : (⊤ : Subgroup E).map q = ⊤ := map_top_of_surjective q (QuotientGroup.mk'_surjective U)
    rw [←ht,←map_commutator]
    change U.map q = ⊥
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  let : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr
    (by simpa only [←Nat.card_eq_fintype_card] using Nat.even_iff.mp heven)
  have hn := GorensteinWalter.PSL2Cover.defining_prime_not_dvd_kernel_of_even F heven hF f hf hc
  rw [hchar] at hn
  have hz : f.ker = ⊥ := hp.card_eq_or_dvd.elim (fun h => Subgroup.card_eq_one.mp h) (fun h => (hn h).elim)
  apply le_antisymm _ hU
  have hm : (pCore 2 E).map q = ⊥ := hk ▸ hz
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm
end Theory.PSL2
