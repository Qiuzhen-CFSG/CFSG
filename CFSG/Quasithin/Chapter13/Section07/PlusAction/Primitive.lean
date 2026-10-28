module

public import Theory.GroupTheory.ChiefKernelSelection
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Residual

/-!
# Primitive lifts in the original star kernel

A nonzero normal subgroup of H/O₂(H) contains either a simple component
or an odd elementary abelian minimal normal subgroup. Lift the component
through the solvable two-core, and in the odd case take the two-residual
of its full preimage. Both constructions give a nontrivial two-perfect
subnormal subgroup of H with its exact image in the prescribed kernel.
The intrinsic quotient is simple in the component case and elementary
abelian in the odd case. No faithfulness assumption enters this selection.

Source: Aschbacher--Smith 13.7.4(1), printed pp.936--937.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

/-- The primitive source alternatives, on the intrinsic quotient of the
actual lifted subgroup and the original star projection. -/
@[expose] def IsPrimitiveLift (H : Subgroup G) (J : Subgroup H) : Prop :=
  (J.IsCComponent ∧ IsSimpleGroup (J ⧸ pCore 2 J)) ∨
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ J.Normal ∧
    ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥ ∧
    IsElementaryAbelian p (J ⧸ pCore 2 J))

/-- Choose a primitive lift inside any nonzero normal star kernel. -/
theorem exists_primitive_lift (H : Subgroup G)
    (C : Subgroup (H ⧸ pCore 2 H)) (hC : C.Normal) (hne : C ≠ ⊥) :
    ∃ J : Subgroup H, J.IsSubnormal ∧ IsPPerfect 2 J ∧ J ≠ ⊥ ∧
      J.map (QuotientGroup.mk' (pCore 2 H)) ≤ C ∧ IsPrimitiveLift H J := by
  classical
  rcases Theory.GroupTheory.exists_simple_component_or_odd_minimal_normal
    C hC hne (pCore_quotient_pCore_eq_bot 2) with hcomp | hodd
  · obtain ⟨E, hEC, hE, hs⟩ := hcomp
    let : IsSimpleGroup E := hs
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    obtain ⟨J, hJ, he⟩ := (Theory.GroupTheory.IsComponent.isCComponent hE).exists_map_quotient_eq (pCore 2 H)
    let : Group.IsPerfect J := hJ.perfect
    let e := (cComponentTwoCoreQuotientEquiv hJ).trans (MulEquiv.subgroupCongr he)
    refine ⟨J, hJ.subnormal, perfect_twoPerfect, ?_, he ▸ hEC, Or.inl ⟨hJ, e.isSimpleGroup⟩⟩
    intro hz
    have hEbot : E = ⊥ := by simpa only [hz, Subgroup.map_bot] using he.symm
    exact (Theory.GroupTheory.IsComponent.isCComponent hE).ne_bot hEbot
  · obtain ⟨p, N, hp, ho, hNC, hc, hE⟩ := hodd
    let : Fact p.Prime := ⟨hp⟩
    let : N.Normal := hc.normal_upper
    let : IsElementaryAbelian p N := hE
    let J := starResidual H N
    have hnp := IsElementaryAbelian.isPGroup p N
    have hi : J.map (QuotientGroup.mk' (pCore 2 H)) = N :=
      starResidual_image H N (odd_pGroup_isTwoPerfect ho hnp)
    have hn : J.Normal := starResidual_normal H N
    let e := oddStarResidualCoreEquiv H N ho hnp
    refine ⟨J, hn.isSubnormal, starResidual_isPPerfect H N, ?_, hi ▸ hNC,
      Or.inr ⟨p, hp, ho, hn, hi.symm ▸ hc,
        IsElementaryAbelian.of_injective e.toMonoidHom e.injective⟩⟩
    intro hz
    have hNbot : N = ⊥ := by simpa only [hz, Subgroup.map_bot] using hi.symm
    exact (ne_of_gt hc.lt) hNbot

/-- Nonfaithfulness selects a primitive subgroup inside the literal lifted
kernel of the quotient representation. -/
theorem exists_primitive_action_kernel (H : Subgroup G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (hne : ¬ Function.Injective σ) :
    ∃ J : Subgroup H, J.IsSubnormal ∧ IsPPerfect 2 J ∧ J ≠ ⊥ ∧
      J ≤ (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker ∧ IsPrimitiveLift H J := by
  have hc : σ.ker ≠ ⊥ := fun he => hne ((MonoidHom.ker_eq_bot_iff σ).mp he)
  obtain ⟨J, hJ, hp, hJne, hle, hm⟩ := exists_primitive_lift H σ.ker inferInstance hc
  exact ⟨J, hJ, hp, hJne, map_le_iff_le_comap.mp hle, hm⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction
