module
public import Theory.GroupTheory.NormalThreeHallCentralizer
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow two-subgroups above a normal ternary plane

A normal elementary subgroup of order nine with two-group quotient is
self-centralizing when the ambient two-core is trivial. Thus a Sylow
two-subgroup acts faithfully on the ternary plane and embeds in GL₂(3).
If its order exceeds eight, its image is a Sylow subgroup of GL₂(3).

The second theorem applies this to the characteristic three-core of a
normal subgroup of index at most two. It retains that subgroup and its
actual prime core, as needed by the quotient-extension argument in
Aschbacher--Smith, 15.3.25.
-/

public section
open Subgroup Matrix
namespace Theory.GroupTheory.NormalNineSylow
variable {H : Type*} [Group H] [Finite H]

/-- A Sylow subgroup of order greater than eight acts as a full Sylow
subgroup on the normal ternary plane. -/
theorem sylow_equiv_of_normal_nine
    (E : Subgroup H) [E.Normal] [IsElementaryAbelian 3 E]
    (hE : Nat.card E = 9) (hO : pCore 2 H = ⊥)
    (hquot : IsPGroup 2 (H ⧸ E))
    (P : Sylow 2 H) (hP : 8 < Nat.card P) :
    ∃ Q : Sylow 2 (GL (Fin 2) (ZMod 3)), Nonempty (P ≃* Q) := by
  classical
  have hthree := IsElementaryAbelian.isPGroup 3 E
  let : Group.IsNilpotent E := hthree.isNilpotent
  let : Group.IsNilpotent (H ⧸ E) := hquot.isNilpotent
  have hsolv : Group.IsSolvable H :=
    (Group.isSolvable_iff_subgroup_quotient E).mpr ⟨inferInstance, inferInstance⟩
  have hc := centralizer_normal_three_le_of_two_quotient hsolv hO E hthree hquot
  let a : P →* MulAut E :=
    (MulAut.conjNormal : H →* MulAut E).comp (P : Subgroup H).subtype
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have he : (x : H) ∈ centralizer (E : Set H) := by
      rw [mem_centralizer_iff]
      intro y hy
      have ht := congrArg (fun e : MulAut E => ((e ⟨y,hy⟩ : E) : H)) hx
      change (x : H) * y * (x : H)⁻¹ = y at ht
      have hh := congrArg (fun z : H => z * (x : H)) ht
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (P : Subgroup H) E
      P.isPGroup' hthree
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hd.le_bot ⟨x.property, hc he⟩)))
  obtain ⟨b,hb⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) E (by omega)
  let f := b.comp a
  have hf : Function.Injective f := hb.comp ha
  let R := (⊤ : Subgroup P).map f
  have hR : IsPGroup 2 R := (P.isPGroup'.to_subgroup ⊤).map f
  obtain ⟨Q,hRQ⟩ := hR.exists_le_sylow
  have hRc : Nat.card R = Nat.card P := by
    rw [card_map_of_injective hf, card_top]
  have hQc : Nat.card Q = 16 := by
    rw [Q.card_eq_multiplicity, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
    decide +kernel
  have hdiv : Nat.card R ∣ 16 := hQc ▸ card_dvd_of_le hRQ
  have hlarge : 8 < Nat.card R := hRc.symm ▸ hP
  have heq : R = (Q : Subgroup (GL (Fin 2) (ZMod 3))) := by
    apply eq_of_le_of_card_ge hRQ
    rw [hQc]
    obtain ⟨k,hk⟩ := hdiv
    have hk2 : k < 2 := by nlinarith
    interval_cases k <;> omega
  refine ⟨Q, ⟨?_⟩⟩
  exact (Subgroup.topEquiv.symm.trans
    ((⊤ : Subgroup P).equivMapOfInjective f hf)).trans (MulEquiv.subgroupCongr heq)

/-- The characteristic ternary plane survives extension by index at most
two, giving the required Sylow model without a splitting assumption. -/
theorem sylow_equiv_of_index_two_nine_core
    (N : Subgroup H) [N.Normal] (hN : N.index ∣ 2)
    [IsElementaryAbelian 3 (pCore 3 N)] (hE : Nat.card (pCore 3 N) = 9)
    (hNquot : IsPGroup 2 (N ⧸ pCore 3 N)) (hO : pCore 2 H = ⊥)
    (P : Sylow 2 H) (hP : 8 < Nat.card P) :
    ∃ Q : Sylow 2 (GL (Fin 2) (ZMod 3)), Nonempty (P ≃* Q) := by
  let E := (pCore 3 N).map N.subtype
  let : E.Normal := inferInstanceAs ((pCore 3 N).map N.subtype).Normal
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map N.subtype
  have hEc : Nat.card E = 9 :=
    (card_map_of_injective N.subtype_injective).trans hE
  have hEq : IsPGroup 2 (H ⧸ E) := by
    obtain ⟨n,hn⟩ := hNquot.exists_card_eq
    apply IsPGroup.of_card_dvd_pow (n := n + 1)
    change E.index ∣ 2 ^ (n + 1)
    rw [show E.index = (pCore 3 N).index * N.index from index_map_subtype _]
    change Nat.card (N ⧸ pCore 3 N) * N.index ∣ 2 ^ (n + 1)
    rw [hn, pow_succ]
    exact Nat.mul_dvd_mul_left _ hN
  exact sylow_equiv_of_normal_nine E hEc hO hEq P hP

end Theory.GroupTheory.NormalNineSylow
