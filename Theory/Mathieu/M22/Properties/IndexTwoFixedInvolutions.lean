module

public import Theory.Mathieu.M22.Basic
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupAction.FourthPowerFixed
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Index-two subgroups of outer M22 fixed groups

For the outer fixed groups of Aschbacher--Smith 16.1.5(5), retain an exact
E8 or E16 kernel, the actual quotient, and the faithful quotient action
compatible with conjugation. The E8 extension of PSL3(2) is perfect.
In the E16 extension of Sz(2), every index-two subgroup contains all
elements whose square is one.

An order-seven or order-five actor fixes only the identity of its kernel,
by orbit counting. Surjectivity of the commutator map puts that kernel in
the derived group. The perfect quotient then proves the first assertion.
For the second, pass to the actual five-four quotient: its involutions
have square roots in the C4 factor, and every C5 element is a square.

No splitting of either full extension is assumed. The comparison of the
actual Sz(2) quotient with the faithful C5 semidirect C4 group is explicit.
`OuterFixedTable` specifies the earlier table input on the full fixed
subgroup of an automorphism of the concrete Witt-design M22; it is not
asserted here. The final source assembly must construct that input.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
16.1.5(5), printed pp.1171--1172, and proof of 16.4.9(2), printed p.1190.
PSL perfectness and the matrix order formula reuse the existing attributed
ATLAS port in Theory/AtlasPort/ExceptionalIsomorphisms.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace Sporadic.Mathieu.M22FixedInvolutions

abbrev Elementary (n : ℕ) := Fin n → Multiplicative (ZMod 2)
abbrev C5 := Multiplicative (ZMod 5)
abbrev C4 := Multiplicative (ZMod 4)
abbrev L3Two := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
noncomputable abbrev SzTwo := BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0

/-- The exact E8 extension with its faithful PSL3(2) conjugation action. -/
structure LinearEightData (E : Type*) [Group E] where
  extension : GroupExtension (Elementary 3) E L3Two
  action : L3Two →* MulAut (Elementary 3)
  faithful : Function.Injective action
  compatible : ∀ x : E, extension.conjAct x = action (extension.rightHom x)

/-- The exact E16 extension, identifying the actual Suzuki quotient and its action. -/
structure SuzukiSixteenData (E : Type*) [Group E] where
  extension : GroupExtension (Elementary 4) E SzTwo
  fiveFourAction : C4 →* MulAut C5
  fiveFourFaithful : Function.Injective fiveFourAction
  quotientEquiv : SzTwo ≃* (C5 ⋊[fiveFourAction] C4)
  action : (C5 ⋊[fiveFourAction] C4) →* MulAut (Elementary 4)
  faithful : Function.Injective action
  compatible : ∀ x : E,
    extension.conjAct x = action (quotientEquiv (extension.rightHom x))

/-- The earlier outer centralizer table, with its actual extension actions. -/
def OuterFixedTable : Prop :=
  ∀ a : MulAut M22, orderOf a = 2 → (¬ ∃ g, a = MulAut.conj g) →
    Nonempty (LinearEightData a.fixedSubgroup) ∨
      Nonempty (SuzukiSixteenData a.fixedSubgroup)

private theorem fixed_proper {V : Type*} [Group V] (a : MulAut V)
    (hne : a ≠ 1) : FixedPoints.subgroup (zpowers a) V ≠ ⊤ := by
  intro htop
  apply hne
  ext v
  exact (MulAut.mem_fixed_zpowers_iff a v).mp (htop ▸ mem_top v)

private theorem fixedPointFree_seven {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 8) (a : MulAut V) (ha : orderOf a = 7) :
    MonoidHom.FixedPointFree a := by
  let C := FixedPoints.subgroup (zpowers a) V
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : IsPGroup 7 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ha, pow_one])
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 7 = Nat.card C % 7 at hmod
  rw [hV] at hmod
  have hle : Nat.card C ≤ 8 := by simpa [hV] using C.card_le_card_group
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hcard : Nat.card C = 1 ∨ Nat.card C = 8 := by omega
  have hbot : C = ⊥ := by
    rcases hcard with h | h
    · exact C.eq_bot_of_card_eq h
    · have hne : a ≠ 1 := by intro he; simp [he] at ha
      exact (fixed_proper a hne (C.eq_top_of_card_eq (h.trans hV.symm))).elim
  intro v hv
  have hm : v ∈ C := (MulAut.mem_fixed_zpowers_iff a v).mpr hv
  rwa [hbot, mem_bot] at hm

private theorem fixedPointFree_five {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (a : MulAut V) (ha : orderOf a = 5) :
    MonoidHom.FixedPointFree a := by
  have hne : a ≠ 1 := by intro he; simp [he] at ha
  have hbot := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen
    (by rw [Nat.card_zpowers, ha]) hV (fixed_proper a hne)
  intro v hv
  have hm := (MulAut.mem_fixed_zpowers_iff a v).mpr hv
  rwa [hbot, mem_bot] at hm

private theorem extension_kernel_le_commutator {N E Q : Type*}
    [Group N] [Finite N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (t : E)
    (ht : MonoidHom.FixedPointFree (S.conjAct t)) : S.rightHom.ker ≤ commutator E := by
  rw [← S.range_inl_eq_ker_rightHom]
  rintro _ ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := ht.commutatorMap_surjective v
  rw [← hw, MonoidHom.commutatorMap_apply, map_div, S.inl_conjAct_comm]
  have hm := commutator_mem_commutator (mem_top (S.inl w)) (mem_top t)
  simpa only [commutator_def, commutatorElement_def, div_eq_mul_inv,
    mul_inv_rev, inv_inv, mul_assoc] using hm

private theorem perfect_of_kernel_le_commutator {E Q : Type*} [Group E] [Group Q]
    [Group.IsPerfect Q] (f : E →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ commutator E) : Group.IsPerfect E := by
  have hmap : (commutator E).map f = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  constructor
  have hc := congrArg (Subgroup.comap f) hmap
  simpa only [comap_map_eq, sup_of_le_left hk, comap_top] using hc

/-- The E₈ extension is perfect, derived from the faithful action. -/
theorem LinearEightData.isPerfect {E : Type*} [Group E] (d : LinearEightData E) :
    Group.IsPerfect E := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hcard : Nat.card L3Two = 168 := by
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 3
    norm_num [Fin.prod_univ_succ] at h
    rw [Nat.card_eq_fintype_card]
    exact h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L3Two) 7
    (by rw [hcard]; decide)
  obtain ⟨t, ht⟩ := d.extension.rightHom_surjective g
  have ho : orderOf (d.extension.conjAct t) = 7 := by
    rw [d.compatible, ht, orderOf_injective d.action d.faithful, hg]
  have hfp := fixedPointFree_seven (by simp [Elementary]) _ ho
  let : Group.IsPerfect L3Two := Atlas.psl_perfect 3 (by decide)
  exact perfect_of_kernel_le_commutator d.extension.rightHom
    d.extension.rightHom_surjective (extension_kernel_le_commutator d.extension t hfp)

/-- The E₁₆ kernel lies in the derived group; no splitting of this extension is used. -/
theorem SuzukiSixteenData.kernel_le_commutator {E : Type*} [Group E]
    (d : SuzukiSixteenData E) : d.extension.rightHom.ker ≤ commutator E := by
  let g : C5 := Multiplicative.ofAdd 1
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hg : orderOf g = 5 := orderOf_eq_prime (by decide) (by decide)
  let y : C5 ⋊[d.fiveFourAction] C4 := SemidirectProduct.inl g
  have hy : orderOf y = 5 :=
    (orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective g).trans hg
  obtain ⟨t, ht⟩ := d.extension.rightHom_surjective (d.quotientEquiv.symm y)
  have ho : orderOf (d.extension.conjAct t) = 5 := by
    rw [d.compatible, ht, d.quotientEquiv.apply_symm_apply,
      orderOf_injective d.action d.faithful, hy]
  exact extension_kernel_le_commutator d.extension t
    (fixedPointFree_five (by simp [Elementary]) _ ho)

private theorem commutator_le_index_two {E : Type*} [Group E]
    (D : Subgroup E) (hD : D.index = 2) : commutator E ≤ D := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  simp only [commutatorElement_def, D.mul_mem_iff_of_index_two hD, D.inv_mem_iff]
  tauto

private theorem five_four_mem_index_two
    (φ : C4 →* MulAut C5) (D : Subgroup (C5 ⋊[φ] C4))
    (hD : D.index = 2) (x : C5 ⋊[φ] C4) (hx : x ^ 2 = 1) : x ∈ D := by
  have hl : SemidirectProduct.inl x.left ∈ D := by
    obtain ⟨z, hz⟩ := (by decide : ∀ y : C5, ∃ z, z ^ 2 = y) x.left
    rw [← hz, map_pow]
    exact D.sq_mem_of_index_two hD _
  have hr : x.right ^ 2 = 1 := by
    have h := congrArg (SemidirectProduct.rightHom (φ := φ)) hx
    simpa only [map_pow, map_one, SemidirectProduct.rightHom_eq_right] using h
  obtain ⟨z, hz⟩ := (by decide : ∀ y : C4, y ^ 2 = 1 → ∃ z, z ^ 2 = y) x.right hr
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply D.mul_mem hl
  rw [← hz, map_pow]
  exact D.sq_mem_of_index_two hD _

/-- Every square-one element of the E₁₆ extension lies in each index-two subgroup. -/
theorem SuzukiSixteenData.mem_of_sq_eq_one {E : Type*} [Group E]
    (d : SuzukiSixteenData E) (D : Subgroup E) (hD : D.index = 2)
    (x : E) (hx : x ^ 2 = 1) : x ∈ D := by
  let f := d.quotientEquiv.toMonoidHom.comp d.extension.rightHom
  have hf : Function.Surjective f := d.quotientEquiv.surjective.comp
    d.extension.rightHom_surjective
  have hk : f.ker ≤ D := by
    intro z hz
    have hz' : z ∈ d.extension.rightHom.ker := by
      apply (map_eq_one_iff d.quotientEquiv d.quotientEquiv.injective).mp
      exact hz
    exact commutator_le_index_two D hD (d.kernel_le_commutator hz')
  have hindex : (D.map f).index = 2 := (D.index_map_eq hf hk).trans hD
  have hm : f x ∈ D.map f := five_four_mem_index_two d.fiveFourAction _ hindex _
    (by rw [← map_pow, hx, map_one])
  have : x ∈ (D.map f).comap f := hm
  rwa [comap_map_eq_self hk] at this

/-- The index-two containment consequence of the precise outer fixed-group table. -/
theorem mem_of_outer_fixed_table (table : OuterFixedTable)
    (a : MulAut M22) (ha : orderOf a = 2) (houter : ¬ ∃ g, a = MulAut.conj g)
    (hnp : ¬ Group.IsPerfect a.fixedSubgroup)
    (D : Subgroup a.fixedSubgroup) (hD : D.index = 2)
    (x : a.fixedSubgroup) (hx : orderOf x = 2) : x ∈ D := by
  rcases table a ha houter with hd | hd
  · obtain ⟨d⟩ := hd
    exact (hnp d.isPerfect).elim
  · obtain ⟨d⟩ := hd
    exact d.mem_of_sq_eq_one D hD x (hx ▸ pow_orderOf_eq_one x)

end Sporadic.Mathieu.M22FixedInvolutions
