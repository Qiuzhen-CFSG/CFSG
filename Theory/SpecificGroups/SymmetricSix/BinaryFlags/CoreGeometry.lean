module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ChiefCubicCores
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Cores of the canonical six-letter flag groups

Relabeling the duad model by `(04)(15)` identifies the point core with
`⟨(45),(01)(23),(02)(13)⟩`; its even part is the Klein four fixing 4 and 5.
The syntheme calculation gives the plane core D and its even part D0.
Both rank-three cores have order eight and are elementary abelian, and
both even cores have order four.

The plane residual has core D0 as an actual subgroup of S₆. The pair
rotation has odd order, so belongs to the residual; its commutators
supply all three nonidentity elements of D0. Relative normality puts the
residual core inside D, and the sign quotient forces it to be even.
This also works for every subgroup between L2 and H2. In particular it
does not identify the plane residual with the different embedded A₄ K.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.3.4, printed pp.84–85, and Notation 13.2.1, printed p.877. The plane
residual marking is also used in 13.8.34. The finite certificates here
use the explicit 48-element disjoint-block model and kernel checking.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- Relabel the library's duad `{0,1}` as the source duad `{4,5}`. -/
def flagRelabel : S := Equiv.swap 0 4 * Equiv.swap 1 5

theorem flagRelabel_even : flagRelabel ∈ alternatingGroup (Fin 6) := by decide

theorem flagRelabel_duad :
    duadStabilizer.map (MulAut.conj flagRelabel).toMonoidHom = H1 := by
  rw [duadStabilizer, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  congr 1

theorem flagRelabel_syntheme :
    H2.map (MulAut.conj flagRelabel).toMonoidHom = H2 := by
  change synthemeStabilizer.map _ = synthemeStabilizer
  rw [synthemeStabilizer, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  congr 1
  decide

theorem conjugate_alternating (g : S) :
    (alternatingGroup (Fin 6)).map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin 6) := by
  exact Subgroup.Normal.map_conj_eq _ g

/-- The line core in explicit disjoint-block coordinates. The second factor
is the Klein four of double transpositions on the complementary four letters. -/
def pointCore : Subgroup S := DuadCalculation.productCore.map
  ((MulAut.conj flagRelabel).toMonoidHom.comp duadProductHom)

theorem H1_core_eq_pointCore : H1.pCoreIn 2 = pointCore := by
  rw [← flagRelabel_duad, ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj flagRelabel).injective]
  unfold pCoreIn pointCore
  rw [← pCore_map_iso 2 duadProductEquiv, ← DuadCalculation.productCore_eq,
    map_map, map_map]
  rfl

/-- The even line core consists of the double transpositions fixing 4 and 5. -/
def pointCoreEven : Subgroup S := pointCore ⊓ alternatingGroup (Fin 6)

private theorem core_normalizes (M : Subgroup S) : M ≤ normalizer (M.pCoreIn 2 : Set S) :=
  M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))

private theorem core_intersection (M N : Subgroup S)
    (hn : M ≤ normalizer (N : Set S)) :
    (M ⊓ N).pCoreIn 2 = M.pCoreIn 2 ⊓ N := by
  apply le_antisymm
  · exact le_inf (pCoreIn_mono_of_normalizes inf_le_left
      ((le_inf M.le_normalizer hn).trans inf_normalizer_le_normalizer_inf))
      ((pCoreIn_le 2 _).trans inf_le_right)
  · exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 M).to_le inf_le_left)
      (inf_le_inf (pCoreIn_le 2 M) le_rfl)
      (inf_le_left.trans ((le_inf (core_normalizes M) hn).trans
        inf_normalizer_le_normalizer_inf))

theorem L1_core_eq_pointCoreEven : L1.pCoreIn 2 = pointCoreEven := by
  rw [L1, core_intersection H1 _ le_normalizer_of_normal, H1_core_eq_pointCore]
  rfl

theorem L2_core_eq_D0 : L2.pCoreIn 2 = D0 := by
  rw [L2, core_intersection H2 _ le_normalizer_of_normal, H2_core_eq_D]
  rfl

private theorem pointCore_coords : ∀ x : DuadProduct,
    x ∈ DuadCalculation.productCore →
      (MulAut.conj flagRelabel) (duadProductHom x) ∈ H1 ⊓ H2 := by
  simp only [DuadCalculation.productCore, mem_prod, mem_top, true_and, DuadCalculation.core_mem_iff, mem_inf]
  decide +kernel

theorem pointCore_le_flag : pointCore ≤ H1 ⊓ H2 := by
  rintro g ⟨x, hx, rfl⟩
  exact pointCore_coords x hx

private theorem even_pointCore_coords : ∀ x : DuadProduct,
    x ∈ DuadCalculation.productCore →
      (MulAut.conj flagRelabel) (duadProductHom x) ∈ alternatingGroup (Fin 6) →
      (MulAut.conj flagRelabel) (duadProductHom x) ∈ K := by
  simp only [DuadCalculation.productCore, mem_prod, mem_top, true_and, DuadCalculation.core_mem_iff]
  decide +kernel

theorem pointCoreEven_le_K : pointCoreEven ≤ K := by
  rintro g ⟨⟨x, hx, rfl⟩, he⟩
  exact even_pointCore_coords x hx he

theorem pointCore_card : Nat.card pointCore = 8 := by
  rw [pointCore, card_map_of_injective
    ((MulAut.conj flagRelabel).injective.comp duadProductHom_injective)]
  exact DuadCalculation.productCore_card

/-- Any embedded residual in S₆ is even, by the actual sign quotient. -/
theorem residual_le_alternating (M : Subgroup S) :
    (pResidual 2 M).map M.subtype ≤ alternatingGroup (Fin 6) := by
  rw [← Equiv.Perm.twoResidual_eq_alternating]
  exact map_pResidual_le 2 M.subtype

private theorem residual_normalizes (M : Subgroup S) :
    M ≤ normalizer (((pResidual 2 M).map M.subtype : Subgroup S) : Set S) :=
  M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pResidual 2 M))

private theorem rotation_mem_residual (M : Subgroup S) (hm : pairRotation ∈ M) :
    pairRotation ∈ (pResidual 2 M).map M.subtype := by
  let x : M := ⟨pairRotation, hm⟩
  have hx : x ^ 3 = 1 := Subtype.ext (show pairRotation ^ 3 = 1 by decide)
  exact ⟨x, mem_pResidual_of_orderOf_coprime
    (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hx) (by decide)), rfl⟩

/-- The rotation's commutators generate the even within-block swaps, inside
both the full and the alternating plane parabolic. -/
theorem D0_le_plane_residual (M : Subgroup S) (hD : D0 ≤ M)
    (hr : pairRotation ∈ M) : D0 ≤ (pResidual 2 M).map M.subtype := by
  let R := (pResidual 2 M).map M.subtype
  have hcomm : ⁅R, M⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp (residual_normalizes M)
  have ha : swap01 * swap23 ∈ D0 := ⟨mul_mem swap01_mem_D swap23_mem_D, by change Equiv.Perm.sign _ = 1; decide⟩
  have hb : swap01 * swap45 ∈ D0 := swap01_swap45_mem_D0
  have hc : swap23 * swap45 ∈ D0 := ⟨mul_mem swap23_mem_D swap45_mem_D, by change Equiv.Perm.sign _ = 1; decide⟩
  have hrot : pairRotation ∈ R := rotation_mem_residual M hr
  intro g hg
  rcases D0_cases hg with rfl | rfl | rfl | rfl
  · exact one_mem R
  · have he : ⁅pairRotation, swap23 * swap45⁆ = swap01 * swap23 := by decide
    rw [← he]
    exact hcomm (commutator_mem_commutator hrot (hD hc))
  · have he : ⁅pairRotation, swap01 * swap23⁆ = swap01 * swap45 := by decide
    rw [← he]
    exact hcomm (commutator_mem_commutator hrot (hD ha))
  · have he : ⁅pairRotation, swap01 * swap45⁆ = swap23 * swap45 := by decide
    rw [← he]
    exact hcomm (commutator_mem_commutator hrot (hD hb))

private theorem plane_residual_core (M : Subgroup S) (hM : M ≤ H2)
    (hn : H2 ≤ normalizer (M : Set S)) (hD : D0 ≤ M) (hr : pairRotation ∈ M) :
    ((pResidual 2 M).map M.subtype).pCoreIn 2 = D0 := by
  let R := (pResidual 2 M).map M.subtype
  have hRM : R ≤ M := map_subtype_le _
  have hR : R ≤ H2 := hRM.trans hM
  have hnR : H2 ≤ normalizer (R : Set S) := hn.trans
    (normalizer_le_normalizer_characteristic_image M (pResidual 2 M))
  apply le_antisymm
  · exact le_inf ((pCoreIn_mono_of_normalizes hR hnR).trans_eq H2_core_eq_D)
      ((pCoreIn_le 2 R).trans (residual_le_alternating M))
  · exact le_pCoreIn_of_normalizes (D_isPGroup.to_le inf_le_left)
      (D0_le_plane_residual M hD hr) (hR.trans H2_normalizes_D0)

/-- The ambient two-core of the *residual* of the plane parabolic is D0. -/
theorem H2_residual_core_eq_D0 :
    ((pResidual 2 H2).map H2.subtype).pCoreIn 2 = D0 :=
  plane_residual_core H2 le_rfl H2.le_normalizer (inf_le_left.trans D_le_H2)
    pairRotation_mem_H2

/-- The alternating plane parabolic has the same residual two-core D0. -/
theorem L2_residual_core_eq_D0 :
    ((pResidual 2 L2).map L2.subtype).pCoreIn 2 = D0 :=
  plane_residual_core L2 inf_le_left
    ((le_inf H2.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf)
    D0_le_L2 ⟨pairRotation_mem_H2, by change Equiv.Perm.sign _ = 1; decide⟩

private abbrev lineA : S := swap01 * swap23
private abbrev lineB : S := Equiv.swap 0 2 * Equiv.swap 1 3

private theorem pointCore_word_cert : ∀ x : DuadProduct,
    x ∈ DuadCalculation.productCore →
    (MulAut.conj flagRelabel) (duadProductHom x) ∈
      ([1, lineA, lineB, lineA * lineB, swap45, swap45 * lineA,
        swap45 * lineB, swap45 * (lineA * lineB)] : List S) := by
  simp only [DuadCalculation.productCore, mem_prod, mem_top, true_and, DuadCalculation.core_mem_iff]
  decide +kernel

private theorem pointCore_swap : swap45 ∈ pointCore := by
  refine ⟨(Equiv.swap 0 1, 1), ?_, ?_⟩
  · change True ∧ (1 : Equiv.Perm (Fin 4)) ∈ DuadCalculation.core
    exact ⟨trivial, one_mem _⟩
  · decide

private theorem pointCore_a : lineA ∈ pointCore := by
  refine ⟨(1, Equiv.swap 0 1 * Equiv.swap 2 3), ?_, ?_⟩
  · change True ∧ _ ∈ DuadCalculation.core
    rw [DuadCalculation.core_mem_iff]
    decide
  · decide

private theorem pointCore_b : lineB ∈ pointCore := by
  refine ⟨(1, Equiv.swap 0 2 * Equiv.swap 1 3), ?_, ?_⟩
  · change True ∧ _ ∈ DuadCalculation.core
    rw [DuadCalculation.core_mem_iff]
    decide
  · decide

/-- The line core in the source's permutation generators. -/
theorem pointCore_eq_closure : pointCore = closure
    {swap45, swap01 * swap23, Equiv.swap 0 2 * Equiv.swap 1 3} := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    change (MulAut.conj flagRelabel) (duadProductHom x) ∈ Subgroup.closure _
    have hw := pointCore_word_cert x hx
    have ha : lineA ∈ closure ({swap45, lineA, lineB} : Set S) := subset_closure (by simp)
    have hb : lineB ∈ closure ({swap45, lineA, lineB} : Set S) := subset_closure (by simp)
    have hc : swap45 ∈ closure ({swap45, lineA, lineB} : Set S) := subset_closure (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact ha
    · exact hb
    · exact mul_mem ha hb
    · exact hc
    · exact mul_mem hc ha
    · exact mul_mem hc hb
    · exact mul_mem hc (mul_mem ha hb)
  · rw [closure_le, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨pointCore_swap, pointCore_a, pointCore_b⟩

private theorem pointCoreEven_words (g : S) :
    g ∈ pointCoreEven ↔ g ∈ ([1, lineA, lineB, lineA * lineB] : List S) := by
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, he⟩
    change (MulAut.conj flagRelabel) (duadProductHom x) ∈ _
    change Equiv.Perm.sign ((MulAut.conj flagRelabel) (duadProductHom x)) = 1 at he
    have hw := pointCore_word_cert x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h <;> rw [h] at he ⊢
    all_goals first | decide | (exfalso; change Equiv.Perm.sign _ = 1 at he; revert he; decide)
  · intro hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ⟨pointCore_a, by change Equiv.Perm.sign _ = 1; decide⟩
    · exact ⟨pointCore_b, by change Equiv.Perm.sign _ = 1; decide⟩
    · exact ⟨mul_mem pointCore_a pointCore_b, by change Equiv.Perm.sign _ = 1; decide⟩

private local instance : Fintype pointCoreEven := Fintype.ofFinset
  ([1, lineA, lineB, lineA * lineB] : List S).toFinset
  (by intro g; rw [List.mem_toFinset]; exact (pointCoreEven_words g).symm)

theorem pointCoreEven_card : Nat.card pointCoreEven = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem pointCore_elementary : IsElementaryAbelian 2 pointCore :=
  IsElementaryAbelian.map _

private theorem elementary_le {E F : Subgroup S} (h : E ≤ F)
    [IsElementaryAbelian 2 F] : IsElementaryAbelian 2 E where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    exact congrArg (fun z : F => (z : S)) (IsMulCommutative.is_comm.comm
      (⟨x.val, h x.property⟩ : F) ⟨y.val, h y.property⟩)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.val (h x.property)))

theorem pointCoreEven_elementary : IsElementaryAbelian 2 pointCoreEven := by
  let := pointCore_elementary
  exact elementary_le inf_le_left

theorem D_elementary : IsElementaryAbelian 2 D := by
  rw [← H2_core_eq_D]
  change IsElementaryAbelian 2 ((pCore 2 synthemeStabilizer).map synthemeStabilizer.subtype)
  let := synthemeCore_elementary
  exact IsElementaryAbelian.map_subtype

theorem D0_elementary : IsElementaryAbelian 2 D0 := by
  let := D_elementary
  exact elementary_le inf_le_left

/-- The residual of the line parabolic retains its actual Klein four. -/
theorem K_core_eq_pointCoreEven : K.pCoreIn 2 = pointCoreEven := by
  have hn : H1 ≤ normalizer (K : Set S) := by
    rw [← residual_H1]
    exact H1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H1 (pResidual 2 H1))
  apply le_antisymm
  · exact le_inf ((pCoreIn_mono_of_normalizes K_le_H1 hn).trans_eq H1_core_eq_pointCore)
      ((pCoreIn_le 2 K).trans inf_le_right)
  · have hnormal : H1 ≤ normalizer (pointCoreEven : Set S) := by
      exact (le_inf (H1_core_eq_pointCore ▸ core_normalizes H1) le_normalizer_of_normal).trans
        inf_normalizer_le_normalizer_inf
    exact le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 H1).of_equiv (MulEquiv.subgroupCongr H1_core_eq_pointCore) |>.to_le inf_le_left)
      pointCoreEven_le_K (K_le_H1.trans hnormal)

/-- Every intermediate plane parabolic has the same residual two-core.
Relative normality follows from its containing the even parabolic. -/
theorem plane_residual_core_of_between (M : Subgroup S)
    (hL : L2 ≤ M) (hM : M ≤ H2) :
    ((pResidual 2 M).map M.subtype).pCoreIn 2 = D0 := by
  have hn : H2 ≤ normalizer (M : Set S) := by
    apply (normal_subgroupOf_iff_le_normalizer hM).mp
    constructor
    intro n hn g
    change (g : S) * (n : S) * (g : S)⁻¹ ∈ M
    change (n : S) ∈ M at hn
    have hc : ⁅(g : S), (n : S)⁆ ∈ M := hL ⟨
      H2.mul_mem (H2.mul_mem (H2.mul_mem g.property n.property)
        (H2.inv_mem g.property)) (H2.inv_mem n.property), by
      change Equiv.Perm.sign ⁅(g : S), (n : S)⁆ = 1
      simp [commutatorElement_def, mul_assoc, mul_left_comm, mul_comm]⟩
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
      using M.mul_mem hc hn
  exact plane_residual_core M hM hn (D0_le_L2.trans hL)
    (hL ⟨pairRotation_mem_H2, by change Equiv.Perm.sign _ = 1; decide⟩)

end Theory.SpecificGroups.SymmetricSix.BinaryFlags
