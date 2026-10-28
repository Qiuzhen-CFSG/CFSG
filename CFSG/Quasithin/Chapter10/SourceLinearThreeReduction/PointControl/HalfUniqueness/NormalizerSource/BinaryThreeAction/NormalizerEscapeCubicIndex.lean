module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeJoinCore
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCoreElementary
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Cubic displacement in the original natural-core branch

When the full MS core is the selected natural factor, the original orbit
moves the original join core onto V. Coprime idempotence then places the
cubic movement of the common core kernel inside the original [V,P] of
order sixteen. The common kernel has index sixteen in Q. Consequently
the actual cubic complement has centralizer index at most 256 in Q.
All groups and the complement are the original parabolic witnesses.
This is a bound in one genuine MS branch, not its terminal exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The original cubic fixes a subgroup of index at most 256 in the
containing core whenever the genuine natural-core branch holds. -/
theorem Data.collapsed_natural_core_cubic_index
    (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hm : ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ = D.fullModule) :
    let Q := (enlargedResidual T L H).pCoreIn 2
    let N := Q ⊓ (localJoin T L).pCoreIn 2
    ⁅N,P⁆ ≤ ⁅D.fullModule,P⁆ ∧ (Q ⊓ centralizer (P : Set G)).relIndex Q ≤ 256 := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let N := Q ⊓ (localJoin T L).pCoreIn 2
  let M := ⁅N,P⁆
  let C := N ⊓ centralizer (P : Set G)
  have hPJ : P ≤ localJoin T L :=
    hi.complement_le.trans ((map_subtype_le _).trans h.le_join)
  have hPQ : P ≤ normalizer (Q : Set G) :=
    (hi.complement_le.trans h.residual_le_enlargedResidual).trans
      ((enlargedResidual T L H).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hPR : P ≤ normalizer ((localJoin T L).pCoreIn 2 : Set G) :=
    hPJ.trans ((localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hPN : P ≤ normalizer (N : Set G) :=
    (le_inf hPQ hPR).trans inf_normalizer_le_normalizer_inf
  have hN2 : IsPGroup 2 N := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card P) (Nat.card N) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) P N hi.odd_complement.isPGroup hN2
  have hid := commutator_closure_coprime_idempotent N (P : Set G)
    (by simpa only [closure_eq] using hPN) (fun p hp =>
      hcop.of_dvd_left (by simpa only [Subgroup.orderOf_mk] using
        _root_.orderOf_dvd_natCard (⟨p,hp⟩ : P)))
  simp only [closure_eq] at hid
  have hMV : M ≤ D.fullModule := by
    rw [←hm]
    exact commutator_mono inf_le_right (hi.complement_le.trans h.residual_le_orbit)
  have hsmall : M ≤ ⁅D.fullModule,P⁆ := by
    exact hid.ge.trans (commutator_mono hMV le_rfl)
  refine ⟨hsmall,?_⟩
  have hMcard : Nat.card M ≤ 16 := by
    rw [←f.cubic_moved_card hPJ hi.odd_complement.isPGroup hP]
    exact Nat.card_le_card_of_injective (inclusion hsmall) (inclusion_injective hsmall)
  let : Group.IsNilpotent N := hN2.isNilpotent
  have hdec : N = M ⊔ C :=
    eq_commutator_sup_centralizer_of_solvable_coprime N P hPN inferInstance hcop
  have hCM : C ≤ normalizer (M : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact (inf_le_left.trans (inf_le_right.trans D.core_centralizes_module)).trans
      (centralizer_le (hMV.trans s.full_eq_local.le))
  have hCN : C.relIndex N ≤ 16 := by
    rw [hdec,relIndex_sup_of_normalizes M C hCM]
    exact (Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card C M)).trans hMcard
  have hNQ : N.relIndex Q = 16 := by
    have hh := h.collapsed_core_centralizer_relIndex f hi hP hc
    rwa [h.core_action_kernel_eq_intersection f] at hh
  have hCQ : C.relIndex Q ≤ 256 := by
    rw [←relIndex_mul_relIndex C N Q inf_le_left inf_le_left,hNQ]
    omega
  have hCQle : C ≤ Q ⊓ centralizer (P : Set G) := inf_le_inf_right _ inf_le_left
  exact (relIndex_le_of_le_left hCQle
    (show C.relIndex Q ≠ 0 from index_ne_zero_of_finite)).trans hCQ

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
