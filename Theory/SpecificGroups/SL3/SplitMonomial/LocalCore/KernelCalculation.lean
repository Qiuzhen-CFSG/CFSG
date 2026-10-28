module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.NormNum

/-!
# A local three-core calculation from a three-point action

Let M have an action on three points with abelian kernel, and a normal
two-subgroup whose centralizer lies in that kernel. If H ≤ M contains a
Sylow two-subgroup of the ambient group, it contains that normal two-subgroup.
Consequently O₃(H) centralizes it and lies in the abelian action kernel.
The kernel's Sylow three-subgroup is characteristic in the kernel and
normal in H, so it is exactly O₃(H).

A nonabelian three-subgroup of H cannot act trivially. The image therefore
has order three or six. When |H| = 27 |T| for a two-group T, the kernel's
three-part, and hence the three-core, has order nine.

Conjugation on the three nonidentity elements of a normal subgroup of
order four constructs the needed action whenever its relative centralizer
is abelian. For the split monomial applications these are the three
diagonal sign involutions. Their construction in the actual matrix
models remains a separate obligation.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, printed p.511 (PDF p.528); the abelian-by-S₃ subgroup in GLS3,
Theorem 6.5.3(b), `refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace Matrix.SL3.SplitMonomial.LocalCore

variable {G : Type*} [Group G] [Finite G]

/-- A three-point action with abelian kernel and a normal two-subgroup
whose centralizer fixes all three points. -/
structure ThreePointStructure (M : Type*) [Group M] where
  action : M →* Equiv.Perm (Fin 3)
  kernel_commutative : IsMulCommutative action.ker
  signs : Subgroup M
  signs_normal : signs.Normal
  signs_two_group : IsPGroup 2 signs
  centralizer_signs_le : centralizer (signs : Set M) ≤ action.ker

private noncomputable def nonidentityAut (V : Type*) [Group V] :
    MulAut V →* Equiv.Perm {v : V // v ≠ 1} where
  toFun f := Equiv.Perm.subtypePerm f.toEquiv (fun _ => by simp)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private theorem nonidentityAut_injective (V : Type*) [Group V] :
    Function.Injective (nonidentityAut V) := by
  intro f g h
  apply MulEquiv.ext
  intro v
  by_cases hv : v = 1
  · simp [hv]
  · exact congrArg Subtype.val (congrArg (fun e => e ⟨v, hv⟩) h)

/-- Conjugation on the three nonidentity elements of a normal subgroup
of order four provides the required three-point action. -/
noncomputable def threePointStructureOfNormalFour (V : Subgroup G) [V.Normal]
    (hV : Nat.card V = 4) (hC : IsMulCommutative (centralizer (V : Set G))) :
    ThreePointStructure G := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hc : Fintype.card {v : V // v ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, hV]
  let e : {v : V // v ≠ 1} ≃ Fin 3 := Fintype.equivFinOfCardEq hc
  let f : G →* Equiv.Perm (Fin 3) := e.permCongrHom.toMonoidHom.comp
    ((nonidentityAut V).comp (MulAut.conjNormal (H := V)))
  have hker : f.ker = centralizer (V : Set G) := by
    ext g
    have heq : f g = 1 ↔ (MulAut.conjNormal (H := V)) g = 1 := by
      constructor
      · intro hg
        apply nonidentityAut_injective V
        apply e.permCongrHom.injective
        change e.permCongrHom (nonidentityAut V (MulAut.conjNormal g)) = 1 at hg
        simpa only [map_one] using hg
      · intro hg
        change e.permCongrHom (nonidentityAut V (MulAut.conjNormal g)) = 1
        rw [hg, map_one, map_one]
    change f g = 1 ↔ g ∈ centralizer (V : Set G)
    rw [heq]
    constructor
    · intro hg v hv
      have hh := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) hg
      change g * v * g⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hg
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change g * (v : G) * g⁻¹ = v
      rw [← hg v v.property, mul_inv_cancel_right]
  exact
    { action := f
      kernel_commutative := hker.symm ▸ hC
      signs := V
      signs_normal := inferInstance
      signs_two_group := IsPGroup.of_card (n := 2) hV
      centralizer_signs_le := hker.ge }

omit [Finite G] in
private theorem range_card_three_or_six (f : G →* Equiv.Perm (Fin 3))
    [IsMulCommutative f.ker]
    (hU : ∃ U : Subgroup G, IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card f.range = 3 ∨ Nat.card f.range = 6 := by
  obtain ⟨U, hU, hnU⟩ := hU
  have hne : U.map f ≠ ⊥ := by
    intro he
    have hle : U ≤ f.ker := by
      intro u hu
      show f u = 1
      have : f u ∈ U.map f := mem_map.mpr ⟨u, hu, rfl⟩
      simpa only [he, mem_bot] using this
    exact hnU (.of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hle ha) (hle hb))
  have hthree : 3 ∣ Nat.card f.range := by
    have hd := (hU.map f).card_eq_or_dvd.resolve_left
      (fun h => hne (card_eq_one.mp h))
    exact hd.trans (card_dvd_of_le (map_le_range f U))
  have hsix : Nat.card f.range ∣ 6 := by
    convert f.range.card_subgroup_dvd_card using 1
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hsix
  omega

private theorem card_core_of_action (f : G →* Equiv.Perm (Fin 3))
    [IsMulCommutative f.ker]
    (V : Subgroup G) [V.Normal] (hV : IsPGroup 2 V)
    (hC : centralizer (V : Set G) ≤ f.ker)
    (hG : (Nat.card G).factorization 3 = 3)
    (hU : ∃ U : Subgroup G, IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 G) = 9 := by
  have hcore : pCore 3 G ≤ f.ker := by
    apply le_trans _ hC
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact commutator_eq_bot_of_disjoint
      (IsPGroup.disjoint_of_coprime pCore_isPGroup hV (by decide))
  have hfac : (Nat.card f.ker).factorization 3 = 2 := by
    have hmul := f.ker.card_mul_index
    rw [index_ker] at hmul
    have hf := congrArg (fun n => n.factorization 3) hmul
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      hG] at hf
    rcases range_card_three_or_six f hU with hr | hr
    · rw [hr] at hf
      norm_num only [Nat.prime_three.factorization, Finsupp.single_eq_same] at hf
      omega
    · rw [hr] at hf
      have h6 : Nat.factorization 6 3 = 1 := by
        change Nat.factorization (2 * 3) 3 = 1
        rw [Nat.factorization_mul (by decide) (by decide)]
        norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
      rw [h6] at hf
      omega
  let P : Sylow 3 f.ker := Sylow.nonempty.some
  have hPcard : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity, hfac]
    norm_num
  have hcoreP : pCore 3 G ≤ P.map f.ker.subtype := by
    have hle : (pCore 3 G).subgroupOf f.ker ≤ P :=
      (pCore_isPGroup.comap_of_injective f.ker.subtype f.ker.subtype_injective).le_sylow_of_normal P
    simpa only [map_subgroupOf_eq_of_le hcore] using map_mono (f := f.ker.subtype) hle
  have hPcore : P.map f.ker.subtype ≤ pCore 3 G :=
    P.map_le_pCore inferInstance inferInstance 3
  rw [le_antisymm hcoreP hPcore, card_map_of_injective f.ker.subtype_injective]
  exact hPcard

/-- In a subgroup containing a full ambient Sylow two-subgroup, a nonabelian
three-subgroup forces a factor of three in the three-point image. The
order equation then makes the intrinsic three-core have order nine. -/
theorem card_core_of_structure (M : Subgroup G) (D : ThreePointStructure M)
    (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M)
    (hU : ∃ U : Subgroup G, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hcard : Nat.card H = 27 * Nat.card T) : Nat.card (pCore 3 H) = 9 := by
  let j : H →* M := inclusion hHM
  have hj : Function.Injective j := inclusion_injective hHM
  let f : H →* Equiv.Perm (Fin 3) := D.action.comp j
  let : IsMulCommutative D.action.ker := D.kernel_commutative
  let : IsMulCommutative f.ker := D.action.ker.comap_injective_isMulCommutative hj
  let : D.signs.Normal := D.signs_normal
  have hVH : D.signs ≤ H.subgroupOf M := by
    have hVT := D.signs_two_group.le_sylow_of_normal (T.subtype (hTH.trans hHM))
    exact hVT.trans (comap_mono hTH)
  let V : Subgroup H := D.signs.comap j
  have hV : IsPGroup 2 V := D.signs_two_group.comap_of_injective j hj
  have hC : centralizer (V : Set H) ≤ f.ker := by
    intro x hx
    apply D.centralizer_signs_le
    rw [mem_centralizer_iff] at hx ⊢
    intro y hy
    let yH : H := ⟨y.val, hVH hy⟩
    have hyH : yH ∈ V := hy
    exact congrArg j (hx yH hyH)
  have hH : (Nat.card H).factorization 3 = 3 := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hcard, hn, Nat.factorization_mul (by decide) (pow_ne_zero _ (by decide)),
      Finsupp.add_apply]
    have h27 : Nat.factorization 27 3 = 3 := by
      change Nat.factorization (3 ^ 3) 3 = 3
      exact Nat.factorization_pow_self Nat.prime_three
    simp [h27, Nat.factorization_pow, Nat.prime_two.factorization]
  apply card_core_of_action f V hV hC hH
  obtain ⟨U, hUH, hU, hnU⟩ := hU
  refine ⟨U.subgroupOf H, hU.comap_of_injective H.subtype H.subtype_injective, ?_⟩
  intro hc
  let : IsMulCommutative (U.subgroupOf H) := hc
  apply hnU
  refine .of_setLike_mul_comm fun a ha b hb => ?_
  exact congrArg Subtype.val
    (setLike_mul_comm (s := U.subgroupOf H)
      (show (⟨a, hUH ha⟩ : H) ∈ U.subgroupOf H from ha)
      (show (⟨b, hUH hb⟩ : H) ∈ U.subgroupOf H from hb))

/-- The core calculation requires only a normal four-subgroup of the
monomial overgroup with abelian relative centralizer. -/
theorem card_core_of_normal_four (M : Subgroup G) (V : Subgroup M) [V.Normal]
    (hV : Nat.card V = 4) (hC : IsMulCommutative (centralizer (V : Set M)))
    (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M)
    (hU : ∃ U : Subgroup G, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hcard : Nat.card H = 27 * Nat.card T) : Nat.card (pCore 3 H) = 9 :=
  card_core_of_structure M (threePointStructureOfNormalFour V hV hC) T H hTH hHM hU hcard

end Matrix.SL3.SplitMonomial.LocalCore
