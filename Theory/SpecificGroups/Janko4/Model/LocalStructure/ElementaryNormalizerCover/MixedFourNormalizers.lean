module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PairCentralizerSplit
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuCase
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.Quasithin.Rank

/-!
# Native mixed four-group normalizers

The nonsingular ABB(3) and AAB(2) configurations are the actual first-centralizer
census rows 4 and 5. The intrinsic splitting identifies their full centralizers
with the product of the original four-group and the embedded residual
intersection, by the literal multiplication map.

Their full normalizers fix the unique involution in the smaller ambient class:
row 4 fixes a, and row 5 fixes the product of its two displayed generators.
The second centralizer calculation places the latter normalizer in a conjugate
of the actual Mathieu local. Conjugating the native representatives proves this
normalizer cover for every nonsingular four-group having a first-class member.
Maximality among TWO-locals gives equality with the selected local.

The radical consumer retains its explicit premise that the whole radical
normalizer normalizes this four-group. It supplies the actual local conjugator,
normalizer restriction, local radicality and intrinsic core identities. No such
four-group-normalization premise is asserted for arbitrary radicals, and this
does not identify the normalizer of a larger elementary subgroup merely because
it contains one of these four-groups.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Table 1, p.487,
and the nonsingular four-group configurations in Section 2.3, p.492.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB


open Cardinality.LocalInvolutionCensus

private theorem first_row_commute (i : Fin 11) : Commute a (eH (representative i)) :=
  (eH_commute_z (representative i)).symm

private theorem first_row_order (i : Fin 11) (hi : i = 4 ∨ i = 5) :
    orderOf (eH (representative i)) = 2 := by
  rcases hi with rfl | rfl
  · obtain ⟨g,hg⟩ := isConj_iff.mp (firstTarget_isConj_representative 4)
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq t).trans InvolutionCentralizers.Second.seed_order
  · obtain ⟨g,hg⟩ := isConj_iff.mp (firstTarget_isConj_representative 5)
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a

private theorem first_row_noninner (i : Fin 11) (hi : i = 4 ∨ i = 5) :
    ¬ InnerRelated a (eH (representative i)) := by
  rw [first_representative_inner_iff]
  rcases hi with rfl | rfl <;> simp

/-- The native ABB(3) and AAB(2) centralizers split along their original
four-groups; the second factor retains both full-centralizer residual maps. -/
noncomputable def firstFourCentralizerEquiv (i : Fin 11) (hi : i = 4 ∨ i = 5) :
    firstFourGroup i × pairInnerKernel a (eH (representative i)) ≃*
      centralizer (firstFourGroup i : Set Model) :=
  pairCentralizerProductEquiv a (eH (representative i)) orderOf_a
    (first_row_order i hi) (first_row_commute i) (first_row_noninner i hi)

/-- The native direct-product equivalence preserves the ambient inclusions. -/
@[simp] theorem firstFourCentralizerEquiv_apply (i : Fin 11) (hi : i = 4 ∨ i = 5)
    (u : firstFourGroup i) (k : pairInnerKernel a (eH (representative i))) :
    (firstFourCentralizerEquiv i hi (u,k) : Model) = (u : Model) * k := by
  apply pairCentralizerProductEquiv_apply

private theorem normalizer_centralizes_unique_class {G : Type*} [Group G]
    (U : Subgroup G) (s : G) (hs : s ∈ U)
    (hunique : ∀ u ∈ U, IsConj s u → u = s) :
    normalizer (U : Set G) ≤ centralizer ({s} : Set G) := by
  intro g hg
  have he : g * s * g⁻¹ = s := hunique _ ((hg s).mp hs) (isConj_iff.mpr ⟨g,rfl⟩)
  exact mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp he)

private theorem first_row_product_class (i : Fin 11) (hi : i = 4 ∨ i = 5) :
    IsConj t (a * eH (representative i)) := by
  have hh := secondTarget_isConj_representative_mul_zH i
  have ht : secondTarget i = t := by rcases hi with rfl | rfl <;> rfl
  rw [ht, map_mul, eH_zH, (first_row_commute i).eq.symm] at hh
  exact hh

/-- The unique first-class involution of native ABB(3) is the literal a. -/
theorem firstFour_four_unique_first (u : Model) (hu : u ∈ firstFourGroup 4)
    (ha : IsConj a u) : u = a := by
  have hsq : eH (representative 4) * eH (representative 4) = 1 := by
    simpa only [pow_two, first_row_order 4 (Or.inl rfl)] using
      pow_orderOf_eq_one (eH (representative 4))
  have hforms := (mem_closure_pair_iff a (eH (representative 4))
    (by simpa only [pow_two] using a_pow_two) hsq (first_row_commute 4) u).mp hu
  rcases hforms with he | he | he | he
  · have hbad := isConj_one_left.mp (he ▸ ha)
    have ho := orderOf_a; simp [hbad] at ho
  · exact he
  · exact (not_isConj_z_t (ha.trans ((he ▸ firstTarget_isConj_representative 4).symm))).elim
  · exact (not_isConj_z_t (ha.trans ((he ▸ first_row_product_class 4 (Or.inl rfl)).symm))).elim

/-- The whole native ABB(3) normalizer lies in the full first involution centralizer. -/
theorem firstFour_four_normalizer_le_first :
    normalizer (firstFourGroup 4 : Set Model) ≤ InvolutionCentralizers.First.centralizer :=
  normalizer_centralizes_unique_class (firstFourGroup 4) a
    (subset_closure (by simp)) firstFour_four_unique_first

/-- The unique second-class involution of native AAB(2) is the actual product. -/
theorem firstFour_five_unique_second (u : Model) (hu : u ∈ firstFourGroup 5)
    (ht : IsConj (a * eH (representative 5)) u) : u = a * eH (representative 5) := by
  have hsq : eH (representative 5) * eH (representative 5) = 1 := by
    simpa only [pow_two, first_row_order 5 (Or.inr rfl)] using
      pow_orderOf_eq_one (eH (representative 5))
  have hsecond := (first_row_product_class 5 (Or.inr rfl)).trans ht
  have hforms := (mem_closure_pair_iff a (eH (representative 5))
    (by simpa only [pow_two] using a_pow_two) hsq (first_row_commute 5) u).mp hu
  rcases hforms with he | he | he | he
  · have hbad := isConj_one_left.mp (he ▸ hsecond)
    have ho : orderOf t = 2 := InvolutionCentralizers.Second.seed_order
    simp [hbad] at ho
  · exact (not_isConj_z_t (he ▸ hsecond).symm).elim
  · exact (not_isConj_z_t ((firstTarget_isConj_representative 5).trans (he ▸ hsecond).symm)).elim
  · exact he

/-- Literal ambient centralization of the unique second-class element. -/
theorem firstFour_five_normalizer_le_second :
    normalizer (firstFourGroup 5 : Set Model) ≤
      centralizer ({a * eH (representative 5)} : Set Model) :=
  normalizer_centralizes_unique_class (firstFourGroup 5) _
    (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
      firstFour_five_unique_second

/-- The AAB(2) normalizer lies in a conjugate of the ACTUAL Mathieu local,
with the same conjugator sending its seed to the distinguished product. -/
theorem firstFour_five_normalizer_mathieu :
    ∃ g : Model, (MulAut.conj g) t = a * eH (representative 5) ∧
      normalizer (firstFourGroup 5 : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (first_row_product_class 5 (Or.inr rfl))
  refine ⟨g,hg,firstFour_five_normalizer_le_second.trans ?_⟩
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom)
    InvolutionCentralizers.Second.ambient_le_max1
  have he := map_centralizer_equiv ({t} : Set Model) (MulAut.conj g)
  rw [Set.image_singleton, show (MulAut.conj g) t = a * eH (representative 5) from hg] at he
  exact he ▸ hm

/-- A nonsingular mixed four-group has its full normalizer in one of the two
existing native locals. All placement maps are actual ambient conjugations. -/
theorem noninner_first_pair_normalizer_cover (x y : Model) (hx : IsConj a x)
    (hy : orderOf y = 2) (hc : Commute x y) (hn : ¬ InnerRelated x y) :
    (∃ g : Model, normalizer (closure ({x,y} : Set Model) : Set Model) ≤
      InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Model, normalizer (closure ({x,y} : Set Model) : Set Model) ≤
      max1.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨i,g,hi,he⟩ := noninner_first_four_group_geometry x y hx hy hc hn
  rw [he, ← map_equiv_normalizer_eq]
  rcases hi with rfl | rfl
  · exact Or.inl ⟨g,map_mono firstFour_four_normalizer_le_first⟩
  · obtain ⟨k,_,hk⟩ := firstFour_five_normalizer_mathieu
    refine Or.inr ⟨g*k, ?_⟩
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hk
    rw [map_map] at hh
    have heq : (MulAut.conj g).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
        (MulAut.conj (g*k)).toMonoidHom := by
      ext v
      simp [mul_assoc]
    rwa [heq] at hh



/-- The native first involution centralizer is an actual two-local. -/
theorem first_centralizer_isTwoLocal : IsTwoLocal InvolutionCentralizers.First.centralizer :=
  isTwoLocal_involution_centralizer orderOf_a

/-- The mixed nonsingular four-group branch at maximal-TWO-local level. -/
theorem maximal_noninner_first_pair_normalizer (M : Subgroup Model)
    (hM : IsMaximalTwoLocal M) (x y : Model) (hx : IsConj a x)
    (hy : orderOf y = 2) (hc : Commute x y) (hn : ¬ InnerRelated x y)
    (hMX : M = normalizer (closure ({x,y} : Set Model) : Set Model)) :
    (∃ g : Model, M = InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Model, M = max1.map (MulAut.conj g).toMonoidHom) := by
  rcases noninner_first_pair_normalizer_cover x y hx hy hc hn with ⟨g,hg⟩ | ⟨g,hg⟩
  · exact Or.inl ⟨g,hM.eq_of_le (first_centralizer_isTwoLocal.map_equiv (MulAut.conj g))
      (hMX ▸ hg)⟩
  · exact Or.inr ⟨g,hM.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g))
      (hMX ▸ hg)⟩

/-- Actual radical restriction in the mixed nonsingular four-group branch.
The whole radical normalizer must normalize the displayed four-group; this
hypothesis is retained and is not asserted for arbitrary radicals. -/
theorem radical_local_of_noninner_first_pair
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (x y : Model) (hx : IsConj a x) (hy : orderOf y = 2)
    (hc : Commute x y) (hn : ¬ InnerRelated x y)
    (hNX : normalizer (P : Set Model) ≤ normalizer (closure ({x,y} : Set Model) : Set Model)) :
    ∃ (M : Subgroup Model) (g : Model), IsTwoLocal M ∧
      (M = InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom ∨
        M = max1.map (MulAut.conj g).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  obtain ⟨M,g,hlocal,hrow,hNM⟩ : ∃ (M : Subgroup Model) (g : Model), IsTwoLocal M ∧
      (M = InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom ∨
        M = max1.map (MulAut.conj g).toMonoidHom) ∧ normalizer (P : Set Model) ≤ M := by
    rcases noninner_first_pair_normalizer_cover x y hx hy hc hn with ⟨g,hg⟩ | ⟨g,hg⟩
    · exact ⟨_,g,first_centralizer_isTwoLocal.map_equiv (MulAut.conj g),Or.inl rfl,hNX.trans hg⟩
    · exact ⟨_,g,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g),Or.inr rfl,hNX.trans hg⟩
  have hPM := P.le_normalizer.trans hNM
  have hN := hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hN
  refine ⟨M,g,hlocal,hrow,hNM,hPM,?_,hP.subgroupOf_of_normalizer_normalizes M hPM hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hcore,map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover
