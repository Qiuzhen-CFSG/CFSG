module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Indices
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Parameters

/-!
# Marked involutions for the Section 16 centralizer argument

The odd centralizer indices of Section 3 place every two-subgroup of the
original two-point stabilizer in the centralizer of a distinguished swapping
involution. Two-centrality supplies a distinguished involution in M fixed
by the same subgroup. These are the simultaneous choices preceding (16E).
All subgroups and conjugators remain in the original ambient group.

Source: GLS4, Chapter 2, (16A)–(16E), using Propositions 3.6 and 4.1.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem twoSubgroup_conjugate_le_of_odd_index
    (H P : Subgroup G) (hP : IsPGroup 2 P) (hindex : Odd H.index) :
    ∃ g : G, P ≤ H.map (MulAut.conj g).toMonoidHom := by
  let : MulAction P (G ⧸ H) := MulAction.compHom (G ⧸ H) P.subtype
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ H)
    (by simpa only [← index_eq_card] using hindex.not_two_dvd_nat)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  refine ⟨g, ?_⟩
  intro x hx
  have he := MulAction.mem_fixedPoints.mp ha ⟨x,hx⟩
  have hm : (x * g)⁻¹ * g ∈ H := QuotientGroup.eq.mp he
  refine ⟨g⁻¹ * x * g, ?_, ?_⟩
  · simpa only [mul_inv_rev, inv_inv, mul_assoc, SetLike.mem_coe] using H.inv_mem hm
  · simp [MulAut.conj_apply, mul_assoc]

/-- Every two-subgroup of M centralizes some distinguished involution in M.
This keeps the whole two-subgroup, rather than just one involution. -/
public theorem twoSubgroup_exists_distinguished_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPM : P ≤ M) :
    ∃ z ∈ Z, z ∈ M ∧ P ≤ centralizer ({z} : Set G) := by
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  let C := (M ⊓ centralizer ({z} : Set G)).subgroupOf M
  have hindex : Odd C.index := action_m_odd h r hz hzM
  obtain ⟨m, hm⟩ := twoSubgroup_conjugate_le_of_odd_index C (P.subgroupOf M)
    (hP.of_equiv (subgroupOfEquivOfLe hPM).symm) hindex
  refine ⟨MulAut.conj (m : G) z, h.invariant _ _ hz,
    M.mul_mem (M.mul_mem m.property hzM) (M.inv_mem m.property), ?_⟩
  intro x hx
  obtain ⟨y, hy, he⟩ := hm (show (⟨x,hPM hx⟩ : M) ∈ P.subgroupOf M from hx)
  have hc : Commute (y : G) z := mem_centralizer_singleton_iff.mp hy.2
  have hmapped := hc.map (MulAut.conj (m : G)).toMonoidHom
  have he' : MulAut.conj (m : G) (y : G) = x := congrArg Subtype.val he
  exact mem_centralizer_singleton_iff.mpr (he' ▸ hmapped.eq)

/-- A two-subgroup of D centralizes a distinguished involution swapping the
same two points; its conjugator is retained inside D. -/
public theorem residualTwoSubgroup_exists_swapping_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPD : P ≤ residualPairStabilizer M t) :
    ∃ d : residualPairStabilizer M t,
      MulAut.conj (d : G) t ∈ Z ∧ MulAut.conj (d : G) t ∉ M ∧
      P ≤ centralizer ({MulAut.conj (d : G) t} : Set G) := by
  let D := residualPairStabilizer M t
  let C := (D ⊓ centralizer ({t} : Set G)).subgroupOf D
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  have hmove : t • (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk 1 := by
    intro he
    exact htM ((baseCoset_stabilizer M) ▸ (MulAction.mem_stabilizer_iff.mpr he))
  have hstab : MulAction.stabilizer G (t • (QuotientGroup.mk 1 : G ⧸ M)) =
      rightConjugate M t := by
    simpa [MulAction.Quotient.smul_mk, smul_eq_mul, (h.involutions t ht).inv_eq_self]
      using conjugateCoset_stabilizer M t
  have hindex : Odd C.index := by
    have he := (sectionThreeIndices_of_productDisconnected h).swapping
      z hz hzM t ht (QuotientGroup.mk 1) hmove
    rw [baseCoset_stabilizer, hstab] at he
    exact he ▸ action_m_odd h r hz hzM
  obtain ⟨d, hd⟩ := twoSubgroup_conjugate_le_of_odd_index C (P.subgroupOf D)
    (hP.of_equiv (subgroupOfEquivOfLe hPD).symm) hindex
  refine ⟨d, h.invariant _ _ ht, ?_, ?_⟩
  · intro hm
    have hh := M.mul_mem (M.mul_mem (M.inv_mem d.property.1) hm) d.property.1
    exact htM (by simpa [MulAut.conj_apply, mul_assoc] using hh)
  · intro x hx
    obtain ⟨y, hy, he⟩ := hd (show (⟨x,hPD hx⟩ : D) ∈ P.subgroupOf D from hx)
    have hc : Commute (y : G) t := mem_centralizer_singleton_iff.mp hy.2
    have hc' := hc.map (MulAut.conj (d : G)).toMonoidHom
    have he' : MulAut.conj (d : G) (y : G) = x := congrArg Subtype.val he
    exact mem_centralizer_singleton_iff.mpr (he' ▸ hc'.eq)

/-- Simultaneous marked involutions for any two-subgroup of the two-point
stabilizer, before the maximal centralizer is selected. -/
public theorem residualTwoSubgroup_exists_marked_pair
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPD : P ≤ residualPairStabilizer M t) :
    ∃ z ∈ Z, z ∈ M ∧ ∃ d : residualPairStabilizer M t,
      MulAut.conj (d : G) t ∈ Z ∧ MulAut.conj (d : G) t ∉ M ∧
      P ≤ centralizer ({z} : Set G) ⊓ centralizer ({MulAut.conj (d : G) t} : Set G) := by
  obtain ⟨z, hz, hzM, hzc⟩ := twoSubgroup_exists_distinguished_centralizer h r P hP
    (hPD.trans inf_le_left)
  obtain ⟨d, hdt, hdtM, htc⟩ := residualTwoSubgroup_exists_swapping_centralizer h r ht htM P hP hPD
  exact ⟨z, hz, hzM, d, hdt, hdtM, le_inf hzc htc⟩

/-- Every involution of D has a centralizer escaping M, with no hypothesis
on the solvability of its distinguished circle. -/
public theorem residualInvolution_centralizer_not_le
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t u : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : IsInvolution u) (huD : u ∈ residualPairStabilizer M t) :
    ¬ centralizer ({u} : Set G) ≤ M := by
  obtain ⟨d, _, hdM, hdc⟩ := residualTwoSubgroup_exists_swapping_centralizer
    h r ht htM (zpowers u) (isPGroup_zpowers_of_involution hu) (zpowers_le.mpr huD)
  intro hle
  exact hdM (hle (mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hdc (mem_zpowers u))).symm))

/-- The maximal centralizer from (16A) comes with actual commuting marked
involutions and the noncontainment needed by Corollary 7.13. -/
public theorem exists_maximal_centralizer_marked_pair
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M) :
    ∃ u ∈ residualPairStabilizer M t, IsInvolution u ∧ u ∉ Z ∧
      (∀ v ∈ residualPairStabilizer M t, IsInvolution v →
        (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard) ∧
      ¬ centralizer ({u} : Set G) ≤ M ∧
      ∃ z ∈ Z, z ∈ M ∧ Commute z u ∧
        ∃ d : residualPairStabilizer M t,
          MulAut.conj (d : G) t ∈ Z ∧ MulAut.conj (d : G) t ∉ M ∧
          Commute (MulAut.conj (d : G) t) u := by
  obtain ⟨u, huD, hu, huZ, hmax⟩ := exists_residualCentralizerTrace_maximal h ha hn htM
  obtain ⟨z, hz, hzM, d, hdt, hdtM, hc⟩ := residualTwoSubgroup_exists_marked_pair
    h r ht htM (zpowers u) (isPGroup_zpowers_of_involution hu) (zpowers_le.mpr huD)
  exact ⟨u, huD, hu, huZ, hmax, residualInvolution_centralizer_not_le h r ht htM hu huD,
    z, hz, hzM, (mem_centralizer_singleton_iff.mp (hc (mem_zpowers u)).1).symm,
    d, hdt, hdtM, (mem_centralizer_singleton_iff.mp (hc (mem_zpowers u)).2).symm⟩

end BenderSuzuki.ZD
