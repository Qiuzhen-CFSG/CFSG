module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Inputs
public import CFSG.Quasithin.Chapter10.SourceFullModuleFusion
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# The small offender when the full module is TI

The equal-order elementary TI-pair theorem equates the two mutual normalizer
orders. Thus every nonidentity offender element has precisely the attained
fixed-space corank on V and acts nontrivially. If |V| > 8, the offender has
order greater than two; the component stabilizer has index at most two,
so it contains a nonidentity offender involution of corank at most two.
Point-centralizer control and the original Thompson fusion supply TI in
the fully moved quiet branch. All conjugates use the original element g.

Source: Aschbacher–Smith I.6.2 and 10.2.12, printed pp.424,754–755.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory
open Chapter3.Section02 ChapterE ChapterI.Section06To08
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Point control and full Thompson fusion make the original full module TI. -/
theorem fullModule_ti_of_point_control
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (hc : ∀ v ∈ D.fullModule, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) :
    IsTISubgroup D.fullModule := by
  apply (isTISubgroup_iff_centralizer_and_fusion _).mpr
  refine ⟨?_,?_⟩
  · intro v hv hn
    simpa only [source_fullModule_normalizer D] using hc v hv hn
  · intro x y hx hy hxy
    obtain ⟨g,hg⟩ := hxy
    obtain ⟨m,hm,he⟩ := source_fullModule_element_fusion D hJ hx hy
      (isConj_iff.mpr ⟨g,hg⟩)
    exact ⟨⟨m,D.maximalLocal_normalizes_fullModule hm⟩,he⟩

/-- Every nonidentity offender element has the attained fixed-space corank. -/
theorem full_ti_offender_fixed_corank
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hti : IsTISubgroup D.fullModule)
    {b : G} (hb : b ∈ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hbM : b ∈ D.maximalLocal) (hb1 : b ≠ 1) :
    subgroupCorank D.fullModule (D.fullModule ⊓ centralizer ({b} : Set G)) =
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
        (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
  let V := D.fullModule
  let P := V.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ normalizer (V : Set G)
  let B := V ⊓ normalizer (P : Set G)
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hp : IsTISubgroup P := hti.map_equiv (MulAut.conj g)
  have hd : Disjoint P V := by
    rcases hti.eq_or_disjoint_conjugate g with he | hd
    · exact (c.outside (by simpa only [source_fullModule_normalizer D] using
        (mem_normalizer_iff_map_conj_eq.mpr he))).elim
    · exact hd
  have hc : Nat.card P = Nat.card V := card_map_of_injective (MulAut.conj g).injective
  have hAB : Nat.card A = Nat.card B :=
    ti_pair_mutual_normalizers_card_eq P V hd hp hti hc
  have he : B = V ⊓ centralizer ({b} : Set G) :=
    ti_pair_opposite_normalizer_eq_centralizer P V hd hp hb
      (D.maximalLocal_normalizes_fullModule hbM) hb1
  have hidx : B.relIndex V = A.relIndex P := by
    have hA := relIndex_mul_card_of_le (show A ≤ P from inf_le_left)
    have hB := relIndex_mul_card_of_le (show B ≤ V from inf_le_left)
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := A))
    rw [hAB,hB,hAB.symm,hA,hc]
  change Nat.log 2 ((V ⊓ centralizer ({b} : Set G)).relIndex V) = _
  rw [←he,hidx]
  change Nat.log 2 ((P ⊓ normalizer (D.fullModule : Set G)).relIndex P) = _
  rw [source_fullModule_normalizer D]
  rfl

/-- A nontrivial element of the opposite TI group cannot centralize the full module. -/
theorem full_ti_offender_not_centralizing
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hti : IsTISubgroup D.fullModule)
    {b : G} (hb : b ∈ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hb1 : b ≠ 1) : b ∉ centralizer (D.fullModule : Set G) := by
  intro hbc
  let V := D.fullModule
  let P := V.map (MulAut.conj g).toMonoidHom
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hp : IsTISubgroup P := hti.map_equiv (MulAut.conj g)
  have hd : Disjoint V P := by
    rcases hti.eq_or_disjoint_conjugate g with he | hd
    · exact (c.outside (by simpa only [source_fullModule_normalizer D] using
        (mem_normalizer_iff_map_conj_eq.mpr he))).elim
    · exact hd.symm
  have hne : P ⊓ centralizer (V : Set G) ≠ ⊥ := by
    intro hz
    exact hb1 (hz.le ⟨hb,hbc⟩)
  have hfull := ti_pair_full_normalizer_of_centralizer_ne_bot V P hd hp hne
  exact c.noncommuting (commutator_eq_bot_iff_le_centralizer.mpr
    (ti_pair_commute_of_full_normalizer V P hd hti hp
      (card_map_of_injective (MulAut.conj g).injective).symm hfull))

/-- Above order eight, the attained offender meets the component normalizer nontrivially. -/
theorem full_ti_exists_small_normalizing_involution
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hti : IsTISubgroup D.fullModule)
    (hsize : 8 < Nat.card D.fullModule) :
    ∃ b ∈ D.fullModule.map (MulAut.conj g).toMonoidHom,
      b ∈ D.maximalLocal ∧ b ∈ normalizer (L : Set G) ∧
      b ^ 2 = 1 ∧ b ∉ centralizer (D.fullModule : Set G) ∧
      subgroupCorank D.fullModule (D.fullModule ⊓ centralizer ({b} : Set G)) ≤ 2 := by
  let V := D.fullModule
  let P := V.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let B := A ⊓ normalizer (L : Set G)
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hi : A.relIndex P ≤ 4 := by
    have he : D.maximalLocal.relIndex P = 2 ^ subgroupCorank P (P ⊓ D.maximalLocal) := by
      rw [subgroupCorank_eq_quotient_finrank,relIndex_eq_two_pow_quotient_finrank P D.maximalLocal]
      congr 1
      rw [inf_subgroupOf_left]
    rw [inf_relIndex_left,he]
    exact Nat.pow_le_pow_right (by decide) c.small
  have hcard : Nat.card P = Nat.card V := card_map_of_injective (MulAut.conj g).injective
  have hA : 2 < Nat.card A := by
    have he := relIndex_mul_card_of_le (show A ≤ P from inf_le_left)
    have hbound := Nat.mul_le_mul_right (Nat.card A) hi
    rw [he,hcard] at hbound
    dsimp only [V] at hbound
    omega
  have hidx : B.relIndex A ≤ 2 := by
    rw [inf_relIndex_left]
    by_cases hAN : A ≤ normalizer (L : Set G)
    · rw [relIndex_eq_one.mpr hAN]
      decide
    obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
    obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hAN
    exact (normalizer_relIndex_eq_two_of_pair A L
      (L.map (MulAut.conj t).toMonoidHom)
      (fun m hm => source_nonnormal_maximal_pair D c.nonnormal ht htn m hm.2)
      a ha (fun he => han (mem_normalizer_iff_map_conj_eq.mpr he))).le
  have hB : B ≠ ⊥ := by
    intro hz
    rw [hz,relIndex_bot_left] at hidx
    omega
  obtain ⟨b,hb,hb1⟩ := B.bot_or_exists_ne_one.resolve_left hB
  refine ⟨b,hb.1.1,hb.1.2,hb.2,elemPow_eq_one_of_isElementaryAbelian b hb.1.1,
    full_ti_offender_not_centralizing D c hti hb.1.1 hb1,?_⟩
  rw [full_ti_offender_fixed_corank D c hti hb.1.1 hb.1.2 hb1]
  exact c.small

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
