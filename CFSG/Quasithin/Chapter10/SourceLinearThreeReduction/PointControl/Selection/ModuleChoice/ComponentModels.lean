module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.RankOneRecognition
public import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal
public import Theory.SpecificGroups.SL3.BinaryOddRankOne

/-!
# Actual component models in the moving-Thompson branch

The local centralizer quotient has a two-group kernel and retains two
distinct conjugate components. Their commuting product and the ambient
quasithin rank bound force every odd-prime rank of the original L/O₂(L)
to be at most one. Intersecting this with its actual full-action B.5 factor
excludes larger SL₃ fields using the split torus. Perfectness excludes S₅.

The remaining groups are binary SL₂ and SL₃(2). The first invokes the
proved natural recognition on the original moved subgroup with its fixed
kernel. The second conclusion is an actual group equivalence, not a claim
that its action has already been recognized. ModuleChoice.Source applies
this reduction to fixed support and the point-selection consumer.
Source: Aschbacher--Smith B.5.6(3), 1.2.1(3) and 10.1.1--2,
printed pp.105,504,741--742.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The original nonnormal component has rank at most one at every odd prime. -/
theorem component_quotient_odd_rank_le_one
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p (L ⧸ pCore 2 L) ≤ 1 := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let A := L.subgroupOf H
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  obtain ⟨hA,hB,hne⟩ := local_action_component_pair D ht htn
  obtain ⟨e⟩ := (local_action_original_component D hn).2
  have hQ : primeRank p (H ⧸ C) ≤ 2 := by
    apply (primeRank_quotient_le_of_isTwoGroup p ho C
      (local_module_kernel_isTwoGroup D hn)).trans
    have hHM : H ≤ D.maximalLocal :=
      sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hHM) (inclusion_injective hHM)).trans
      ((D.simpleQTKE.twoLocal_sqtk
        (source_module_nonsolvable_uniqueness D).normalizer_maximal.1).stronglyQuasithin p hp ho)
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  let : IsSimpleGroup (A.map q) := e.isSimpleGroup
  let : Group.IsPerfect (A.map q) := hA.2.toIsPerfect
  have hz : center (A.map q) = ⊥ := by
    rcases (inferInstance : (center (A.map q)).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · exact (Group.IsPerfect.not_isMulCommutative (A.map q) (center_eq_top_iff.mp he)).elim
  rw [← primeRank_equiv p e]
  by_contra! hr
  have hnormal : (A.map q).Normal := hA.normal_of_centerless_of_primeRank hz p (by
    change primeRank p (H ⧸ C) < 2 * primeRank p (A.map q)
    change 1 < primeRank p (A.map q) at hr
    omega)
  apply hne
  have hBq : B.map q = (A.map q).map (MulAut.conj (q tH)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  exact hBq.trans ((normal_iff_map_conj_eq.mp hnormal) (q tH)) |>.symm


private theorem source_factor_binary_models
    {Q V : Type*} [Group Q] [Finite Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q} [Group.IsPerfect A]
    {U : Subrepresentation ρ} (h : ChapterB.SourceInduction.SourceFactorCase ρ A U)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p A ≤ 1) :
    (∃ E : BinaryField, Nonempty (A ≃* SL(2,E.Carrier))) ∨
      Nonempty (A ≃* SL(3,ZMod 2)) := by
  have hthree (E : BinaryField) (e : A ≃* SL(3,E.Carrier)) :
      Nonempty (A ≃* SL(3,ZMod 2)) := by
    have hE : E.degree = 1 := Matrix.SL3.BinaryOddRankOne.degree_eq_one_of_odd_primeRanks_le_one
      E.Carrier E.degree_pos E.card_eq (by
      intro p hp ho
      rw [←primeRank_equiv p e]
      exact hr p hp ho)
    exact ⟨e.trans (ChapterB.QuasisimpleSource.ExtensionConsequences.degreeOneNaturalEquiv
      E hE 3).groupEquiv⟩
  cases h with
  | natural _ hn =>
    cases hn with
    | linearTwo E he => exact Or.inl ⟨E,⟨he.some.groupEquiv⟩⟩
    | linearThree E _ he => exact Or.inr (hthree E he.some.groupEquiv)
    | symmetricFive he =>
      let e := he.some.groupEquiv
      let : Group.IsPerfect (Equiv.Perm (Fin 5)) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      have hc := Group.IsPerfect.commutator_eq_top (G := Equiv.Perm (Fin 5))
      have hle := alternatingGroup.commutator_perm_le (α := Fin 5)
      rw [hc] at hle
      have ht : alternatingGroup (Fin 5) = ⊤ := top_unique hle
      have hs := ht.ge (show Equiv.swap (0 : Fin 5) 1 ∈
        (⊤ : Subgroup (Equiv.Perm (Fin 5))) from mem_top _)
      rw [Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_swap (by decide)] at hs
      exact ((by decide : (-1 : ℤˣ) ≠ 1) hs).elim
  | doubleNatural E _ _ he => exact Or.inr (hthree E he.some.groupEquiv)
  | exceptional _ c => exact Or.inr ⟨c.natural.groupEquiv⟩

set_option backward.isDefEq.respectTransparency false in
/-- Moving local Thompson leaves a recognized rank-one module or an actual
binary-three component. The latter action still requires recognition. -/
theorem rankOneNatural_or_binaryThree_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    RankOneNatural D ∨ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let A := ((L.subgroupOf M).map q).subgroupOf Y
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hAX : L.subgroupOf M ≤ (localOrbit T L).subgroupOf M :=
    comap_mono (le_componentOrbit L T)
  have hAY : (L.subgroupOf M).map q ≤ Y :=
    (map_mono (f := q) hAX).trans (full_orbit_image_le_offender D hJ)
  have hA : IsComponent Y A := (full_action_component_pair D ht htn).1.subgroupOf hAY
  obtain ⟨a⟩ := full_action_original_component_equiv D hn
  let f : A ≃* (L ⧸ pCore 2 L) := (subgroupOfEquivOfLe hAY).trans a
  have hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p A ≤ 1 := by
    intro p hp ho
    rw [primeRank_equiv p f]
    exact component_quotient_odd_rank_le_one D hn p hp ho
  obtain ⟨d⟩ := full_module_two_factor_case D hn hJ
  have hex : ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp Y.subtype),
      d.first = A := by
    rcases full_module_factor_alignment D hna hJ ht htn d with ⟨ha,_⟩ | ⟨ha,_⟩
    · exact ⟨d,ha.symm⟩
    · let ds : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp Y.subtype) := {
        first := d.second
        second := d.first
        product := d.product.swap
        firstSpace := d.secondSpace
        secondSpace := d.firstSpace
        decomposition := d.decomposition.symm
        firstCase := d.secondCase
        secondCase := d.firstCase }
      exact ⟨ds,ha.symm⟩
  obtain ⟨d,hd⟩ := hex
  have hdA : IsComponent Y d.first := hd.symm ▸ hA
  let : Group.IsPerfect d.first := hdA.2.toIsPerfect
  have hm := source_factor_binary_models d.firstCase (hd.symm ▸ hr)
  let aD : (L ⧸ pCore 2 L) ≃* d.first := f.symm.trans (MulEquiv.subgroupCongr hd).symm
  rcases hm with h | h
  · obtain ⟨F,⟨e⟩⟩ := h
    exact Or.inl (rankOneNatural_of_binary_component D hn hna hJ (aD.trans e))
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨aD.trans e⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
