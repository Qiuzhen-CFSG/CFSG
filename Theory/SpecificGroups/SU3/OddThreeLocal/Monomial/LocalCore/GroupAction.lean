module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Three-cores from a three-point action

A nonabelian three-subgroup has nontrivial image under an action with abelian
kernel. For a three-point action the image therefore has three-part three.
If the whole three-core lies in the kernel, it is the kernel's Sylow
three-subgroup. Thus a group with three-part 27 has three-core of order nine.

A normal two-subgroup whose centralizer lies in the action kernel forces
this containment in every overgroup of an ambient Sylow two-subgroup.
The action and normal two-subgroup descend through a central three-group
kernel; the latter meets the two-subgroup trivially.

These are the finite-group calculations for the monomial unitary case of
GLS3, Theorem 6.5.3(b), and Aschbacher–Smith, Proposition 1.3.4, printed p.511.
They do not assert the existence of a matrix action or of its sign subgroup.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial.CoreCalculation

section FiniteCalculation

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem range_three_part (f : G →* Equiv.Perm (Fin 3))
    [IsMulCommutative f.ker]
    (hU : ∃ U : Subgroup G, IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    (Nat.card f.range).factorization 3 = 1 := by
  obtain ⟨U, hU, hnon⟩ := hU
  have hn : U.map f ≠ ⊥ := by
    intro hbot
    have hle := (U.map_eq_bot_iff).mp hbot
    exact hnon (.of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (hle ha) (hle hb))
  have hthree : 3 ∣ Nat.card (U.map f) :=
    (hU.map f).card_eq_or_dvd.resolve_left (fun h => hn (Subgroup.card_eq_one.mp h))
  have hthree' : 3 ∣ Nat.card f.range :=
    hthree.trans (card_dvd_of_le (Subgroup.map_le_range _ _))
  have hsix : Nat.card f.range ∣ 6 := by
    convert f.range.card_subgroup_dvd_card using 1
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hcases : Nat.card f.range = 3 ∨ Nat.card f.range = 6 := by
    have := Nat.le_of_dvd (by decide : 0 < 6) hsix
    have := Nat.card_pos (α := f.range)
    omega
  rcases hcases with h | h
  · rw [h]
    norm_num
  · rw [h, show 6 = 2 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply]
    norm_num

theorem core_card_of_abelian_kernel (f : G →* Equiv.Perm (Fin 3))
    [IsMulCommutative f.ker] (hcore : pCore 3 G ≤ f.ker) :
    Nat.card (pCore 3 G) = 3 ^ (Nat.card f.ker).factorization 3 := by
  let P : Sylow 3 f.ker := default
  have hPcore : (P : Subgroup f.ker).map f.ker.subtype ≤ pCore 3 G :=
    P.map_le_pCore inferInstance inferInstance 3
  have hrev : pCore 3 G ≤ (P : Subgroup f.ker).map f.ker.subtype := by
    intro x hx
    have hmem : (⟨x, hcore hx⟩ : f.ker) ∈ (pCore 3 G).subgroupOf f.ker := hx
    have hle : (pCore 3 G).subgroupOf f.ker ≤ (P : Subgroup f.ker) :=
      (pCore_isPGroup.comap_of_injective f.ker.subtype f.ker.subtype_injective).le_sylow_of_normal P
    exact ⟨⟨x, hcore hx⟩, hle hmem, rfl⟩
  rw [le_antisymm hrev hPcore, card_map_of_injective f.ker.subtype_injective]
  exact P.card_eq_multiplicity

theorem core_card_nine (f : G →* Equiv.Perm (Fin 3))
    [IsMulCommutative f.ker] (hcore : pCore 3 G ≤ f.ker)
    (hcard : (Nat.card G).factorization 3 = 3)
    (hU : ∃ U : Subgroup G, IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 G) = 9 := by
  have hrange := range_three_part f hU
  have hcount := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hcount
  have hf := congrArg (fun n : ℕ => n.factorization 3) hcount
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, hrange, hcard] at hf
  have hk : (Nat.card f.ker).factorization 3 = 2 := by omega
  rw [core_card_of_abelian_kernel f hcore, hk]
  norm_num

omit [Group G] [Finite G] in
theorem three_part_of_card_eq {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (hcard : Nat.card G = 27 * Nat.card T) :
    (Nat.card G).factorization 3 = 3 := by
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hcard, hn, Nat.factorization_mul (by decide) (by positivity), Finsupp.add_apply]
  norm_num [Nat.factorization_pow, Nat.Prime.factorization, Finsupp.single_apply]
  exact Nat.factorization_pow_self (n := 3) (by decide : Nat.Prime 3)

theorem core_card_nine_of_normal_two_subgroup
    (M H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M)
    (f : M →* Equiv.Perm (Fin 3)) [IsMulCommutative f.ker]
    (V : Subgroup M) [V.Normal] (hV : IsPGroup 2 V)
    (hcentral : centralizer (V : Set M) ≤ f.ker)
    (hcard : Nat.card H = 27 * Nat.card T)
    (hU : ∃ U : Subgroup G, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 H) = 9 := by
  let i : H →* M := inclusion hHM
  let a := f.comp i
  have ha : IsMulCommutative a.ker := by
    change IsMulCommutative (f.comp i).ker
    rw [← MonoidHom.comap_ker]
    exact f.ker.comap_injective_isMulCommutative (inclusion_injective hHM)
  have hVT : V ≤ (T.subtype (hTH.trans hHM) : Subgroup M) :=
    hV.le_sylow_of_normal _
  let VH : Subgroup H := V.comap i
  have hVH : VH ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, hV.comap_of_injective i (inclusion_injective hHM)⟩
  have hc : pCore 3 H ≤ a.ker := by
    intro x hx
    apply hcentral
    intro v hv
    have hvH : (v : G) ∈ H := hTH (hVT hv)
    let vH : H := ⟨v, hvH⟩
    have hvcore : vH ∈ pCore 2 H := hVH hv
    exact congrArg i (pCore_commute_of_ne 2 3 (by decide) vH hvcore x hx)
  apply core_card_nine a hc (three_part_of_card_eq T.isPGroup' hcard)
  obtain ⟨U, hUH, hU, hnon⟩ := hU
  refine ⟨U.subgroupOf H, hU.comap_subtype, ?_⟩
  intro hab
  have hmap : (U.subgroupOf H).map H.subtype = U :=
    map_subgroupOf_eq_of_le hUH
  apply hnon
  rw [← hmap]
  infer_instance



end FiniteCalculation

variable {G Q : Type*} [Group G] [Group Q]

theorem descend_action (f : G →* Equiv.Perm (Fin 3)) [IsMulCommutative f.ker]
    (V : Subgroup G) [V.Normal] (hV : IsPGroup 2 V)
    (hcentral : centralizer (V : Set G) ≤ f.ker)
    (q : G →* Q) (hq : Function.Surjective q)
    (hqcentral : q.ker ≤ center G) (hqthree : IsPGroup 3 q.ker) :
    ∃ a : Q →* Equiv.Perm (Fin 3), IsMulCommutative a.ker ∧
      ∃ W : Subgroup Q, W.Normal ∧ IsPGroup 2 W ∧
        centralizer (W : Set Q) ≤ a.ker := by
  have hVnormal : V.Normal := inferInstance
  have hker : q.ker ≤ f.ker := by
    intro x hx
    apply hcentral
    intro v _
    exact mem_center_iff.mp (hqcentral hx) v
  let a : Q →* Equiv.Perm (Fin 3) := q.liftOfSurjective hq ⟨f, hker⟩
  have ha (x : G) : a (q x) = f x := by
    simp [a, MonoidHom.liftOfSurjective]
  have haka : a.ker = f.ker.map q := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hq x
      refine ⟨y, ?_, rfl⟩
      change f y = 1
      change a (q y) = 1 at hx
      rwa [ha] at hx
    · rintro ⟨y, hy, rfl⟩
      change a (q y) = 1
      rw [ha]
      exact hy
  have hab : IsMulCommutative a.ker := by
    rw [haka]
    infer_instance
  refine ⟨a, hab, V.map q, hVnormal.map q hq, hV.map q, ?_⟩
  have hdis : Disjoint V q.ker := hV.disjoint_of_coprime hqthree (by decide)
  have hinj : ∀ {x y : G}, x ∈ V → y ∈ V → q x = q y → x = y := by
    intro x y hx hy hxy
    apply mul_inv_eq_one.mp
    exact (hdis.le_bot ⟨V.mul_mem hx (V.inv_mem hy), by
      change q (x * y⁻¹) = 1
      simp only [map_mul, map_inv, hxy, mul_inv_cancel]⟩ :
        x * y⁻¹ ∈ (⊥ : Subgroup G))
  intro x hx
  obtain ⟨y, rfl⟩ := hq x
  have hy : y ∈ centralizer (V : Set G) := by
    intro v hv
    have hqeq : q (y * v * y⁻¹) = q v := by
      rw [map_mul, map_mul, map_inv, ← hx (q v) (mem_map_of_mem q hv)]
      group
    have heq : y * v * y⁻¹ = v := hinj (hVnormal.conj_mem v hv y) hv hqeq
    calc
      v * y = (y * v * y⁻¹) * y := by rw [heq]
      _ = y * v := by group
  change a (q y) = 1
  rw [ha]
  exact hcentral hy

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial.CoreCalculation
