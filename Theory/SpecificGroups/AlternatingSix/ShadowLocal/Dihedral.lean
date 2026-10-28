module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The dihedral Sylow subgroups of A₆

The even permutations (0123)(45) and (02)(45) give an injective
homomorphism D₈ → A₆. Order and Sylow conjugacy identify every Sylow
two-subgroup of A₆ with D₈, hence also the intersection of a Sylow
two-subgroup of Aut(A₆) with Inn(A₆).

The final theorem checks a source-boundary issue on printed p.567 of
Aschbacher–Smith, *The Classification of Quasithin Groups*. This normal
inner D₈ has derived subgroup of order two. Thus the displayed dichotomy
there cannot hold for every normal subgroup of the Sylow group, since
its nonabelian alternative requires derived subgroup of order four.
The automorphism-prime restriction needed for Lemma 2.5.22 is a separate
claim; the obstruction here does not refute that lemma.
-/

@[expose] public section

namespace AlternatingSix.ShadowLocal
open Subgroup

/-- The even rotation (0123)(45), for the marked dihedral embedding. -/
def dihedralRotation : A6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

/-- The even reflection (02)(45), for the marked dihedral embedding. -/
def dihedralReflection : A6 :=
  ⟨Equiv.swap 0 2 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

def dihedralEmbedding : DihedralGroup 4 →* A6 where
  toFun
    | .r i => dihedralRotation ^ i.val
    | .sr i => dihedralReflection * dihedralRotation ^ i.val
  map_one' := rfl
  map_mul' := by decide +kernel

theorem dihedralEmbedding_injective : Function.Injective dihedralEmbedding := by
  decide +kernel

private theorem card_range_dihedral : Nat.card dihedralEmbedding.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective dihedralEmbedding_injective).toEquiv,
    DihedralGroup.nat_card]

theorem alternatingSylow_card (P : Sylow 2 A6) : Nat.card P = 8 := by
  rw [P.card_eq_multiplicity, card_A6]
  rw [show 360 = 2 ^ 3 * 45 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
  rfl

theorem alternatingSylow_dihedral (P : Sylow 2 A6) : Nonempty (P ≃* DihedralGroup 4) := by
  have hp : IsPGroup 2 dihedralEmbedding.range :=
    IsPGroup.of_card (show Nat.card dihedralEmbedding.range = 2 ^ 3 from card_range_dihedral)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have he : dihedralEmbedding.range = (Q : Subgroup A6) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [card_range_dihedral, alternatingSylow_card])
  exact ⟨(P.equiv Q).trans ((MulEquiv.subgroupCongr he.symm).trans
    (MonoidHom.ofInjective dihedralEmbedding_injective).symm)⟩

theorem sylowInner_dihedral (P : Sylow 2 AutA6) :
    Nonempty (sylowInner P ≃* DihedralGroup 4) := by
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal inner
  let Q' : Sylow 2 A6 := Q.mapSurjective (f := innerEquiv.symm.toMonoidHom) innerEquiv.symm.surjective
  obtain ⟨e⟩ := alternatingSylow_dihedral Q'
  let swap : sylowInner P ≃* (P : Subgroup AutA6).subgroupOf inner := {
    toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact ⟨swap.trans ((MulEquiv.subgroupCongr hQ.symm).trans
    (((Q : Subgroup inner).equivMapOfInjective innerEquiv.symm.toMonoidHom
      innerEquiv.symm.injective).trans e))⟩

open scoped commutatorElement

private theorem dihedralEight_commutator :
    commutator (DihedralGroup 4) = zpowers (DihedralGroup.r 2) := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x _ y _
    have h : ∀ x y : DihedralGroup 4, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = DihedralGroup.r 2 := by
      decide +kernel
    rcases h x y with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers _
  · apply zpowers_le.mpr
    have h : ⁅DihedralGroup.sr (0 : ZMod 4), DihedralGroup.r (1 : ZMod 4)⁆ = DihedralGroup.r 2 := by
      decide +kernel
    rw [← h]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)

private theorem dihedralEight_commutator_card : Nat.card (commutator (DihedralGroup 4)) = 2 := by
  rw [dihedralEight_commutator, Nat.card_zpowers, DihedralGroup.orderOf_r]
  decide

theorem sylowInner_commutator_card (P : Sylow 2 AutA6) :
    Nat.card (commutator (sylowInner P)) = 2 := by
  obtain ⟨e⟩ := sylowInner_dihedral P
  have hm : (commutator (sylowInner P)).map e.toMonoidHom =
      commutator (DihedralGroup 4) := by
    rw [map_commutator_eq, e.toMonoidHom.range_eq_top.mpr e.surjective]
    rfl
  calc
    Nat.card (commutator (sylowInner P)) =
        Nat.card ((commutator (sylowInner P)).map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective e.injective).symm
    _ = 2 := by rw [hm, dihedralEight_commutator_card]

/-- The unrestricted normal-subgroup dichotomy suggested by the p.567
prose fails: the inner dihedral subgroup is normal and nonabelian, but
its derived subgroup has order two, not four. This does not refute
Lemma 2.5.22; its automorphism-prime conclusion needs a different proof
or further source hypotheses for the intermediate dichotomy. -/
theorem normal_subgroup_dichotomy_obstruction (P : Sylow 2 AutA6)
    (Y : Subgroup P) (hY : Nat.card Y = 4) :
    ∃ R : Subgroup P, R.Normal ∧ ¬ IsMulCommutative R ∧ ⁅R, R⁆ ≠ Y := by
  refine ⟨sylowInner P, inferInstance, ?_, ?_⟩
  · intro h
    have hc := sylowInner_commutator_card P
    rw [(commutator_eq_bot_iff (sylowInner P)).mpr h, Subgroup.card_bot] at hc
    contradiction
  · intro he
    have hc : Nat.card (⁅sylowInner P, sylowInner P⁆ : Subgroup P) = 2 := by
      rw [← Subgroup.map_subtype_commutator, Subgroup.card_map_of_injective
        (sylowInner P).subtype_injective]
      exact sylowInner_commutator_card P
    rw [he, hY] at hc
    contradiction

end AlternatingSix.ShadowLocal
