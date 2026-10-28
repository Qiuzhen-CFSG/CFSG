module
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryQuotient
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import CFSG.Quasithin.MainConverse.SolvableSections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.OriginalAction.F4OriginalCore

/-!
# Original binary F4 input clauses apart from MS3

The explicit Levi certificate identifies the original matrix quotient with
`SL₃(2)`. The quotient and component calculations then certify the SQTK,
generalized-Fitting, product, genuine C-component, odd-index radical and
literal component quotient clauses for `BinaryMS.Input`. The MS3 clause is
retained as an explicit argument: this module does not turn the existing
characteristic-subgroup theorem for the replacement parabolic into original
centrality or MS3.

The source carrier is the concrete matrix group from `BinaryCoordinates`.
The checked noncentrality witness is included only as a diagnostic until MS3
is established on this same carrier and its actual Sylow subgroup.

Sources: Aschbacher--Smith C.1.31--34, printed pp.135--137; the F4
coordinates and binary example are those cited in `BinaryLevi`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
open Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates
open CFSG.KnownSimple

private theorem solvable_known {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] :
    IsKGroup IsKnownSimple G := by
  intro S _ hs U f hf
  let := hs
  let : Finite S := Finite.of_surjective f hf
  let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
  exact ⟨inferInstance, hs, .cyclic (MainConverse.primeCyclic_of_solvable_simple S)⟩

private theorem SL_known : IsKnownSimple Matrix.PSL3Two.SL := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  refine ⟨inferInstance, inferInstance, .classical (.linear 3 2 ?_ ?_)⟩
  · exact ⟨(show Nat.Prime 2 by decide).isPrimePow, by decide, by omega⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨Matrix.PSL3Two.equiv⟩⟩

private theorem SL_known_sections : IsKGroup IsKnownSimple Matrix.PSL3Two.SL := by
  intro S _ hs U f hf
  let := hs
  let : Finite S := Finite.of_surjective f hf
  by_cases ht : U = ⊤
  · subst U
    let := Atlas.Comparisons.Exceptional.sl3Two_simple
    let g : Matrix.PSL3Two.SL →* S := f.comp (topEquiv.symm.toMonoidHom)
    have hg : Function.Surjective g := hf.comp topEquiv.symm.surjective
    have hi : Function.Injective g := by
      apply (MonoidHom.ker_eq_bot_iff g).mp
      rcases (inferInstance : g.ker.Normal).eq_bot_or_eq_top with hk | hk
      · exact hk
      · obtain ⟨y, hy⟩ := exists_ne (1 : S)
        obtain ⟨x, rfl⟩ := hg y
        have hx : x ∈ g.ker := hk.symm ▸ mem_top x
        exact (hy hx).elim
    exact SL_known.of_mulEquiv (MulEquiv.ofBijective g ⟨hi,hg⟩).symm
  · let := Matrix.PSL3Two.isSolvable_subgroup_SL_of_ne_top U ht
    let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
    exact ⟨inferInstance, hs, .cyclic (MainConverse.primeCyclic_of_solvable_simple S)⟩

/-- Full SQTK holds for the original matrix overgroup and full known-simple catalogue. -/
theorem original_sqtk : IsSQTK KnownSimple.IsKnownSimple P := by
  refine ⟨?_, ?_⟩
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact QuotientModel.odd_primeRank_le_two p ho
  · refine IsKGroup.of_normal_quotient (K := IsKnownSimple) (E.subgroupOf P) ?_ ?_
    · let : Group.IsNilpotent (E.subgroupOf P) :=
        (E_isPGroup.comap_of_injective P.subtype P.subtype_injective).isNilpotent
      exact solvable_known (G := E.subgroupOf P)
    · exact SL_known_sections.of_injective QuotientModel.quotientEquiv.toMonoidHom
        QuotientModel.quotientEquiv.injective

private noncomputable def coreQuotientCongr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : (G ⧸ pCore 2 G) ≃* (H ⧸ pCore 2 H) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private noncomputable def subgroupCoreQuotientCongr {G : Type*} [Group G]
    (H K : Subgroup G) (h : H ≤ K) :
    ((H.subgroupOf K) ⧸ pCore 2 (H.subgroupOf K)) ≃* (H ⧸ pCore 2 H) :=
  coreQuotientCongr (subgroupOfEquivOfLe h)

/-- The exact intrinsic quotient for the subgroup used by BinaryMS.Input. -/
noncomputable def original_component_quotient :
    ((L.subgroupOf P) ⧸ pCore 2 (L.subgroupOf P)) ≃* Matrix.PSL3Two.SL :=
  (subgroupCoreQuotientCongr L P L_le_P).trans QuotientModel.componentQuotientEquiv

/-- The centrality failure persists with SQTK, characteristic two, a genuine
C-component and the actual simple quotient. The MS3 clause for a suitable
radical remains to be certified; this is not a full source counterexample. -/
theorem original_binaryCore_sqtk_component_diagnostic :
    IsSQTK KnownSimple.IsKnownSimple P ∧
    Theory.GroupTheory.generalizedFitting P = pCore 2 P ∧
    (L.subgroupOf P).IsCComponent ∧
    Nonempty (((L.subgroupOf P) ⧸ pCore 2 (L.subgroupOf P)) ≃* Matrix.PSL3Two.SL) ∧
    ¬ BinaryMS.commutatorCore (L.subgroupOf P) ⊓
      centralizer (L.subgroupOf P : Set P) ≤ centralizer (pCore 2 P : Set P) :=
  ⟨original_sqtk, QuotientModel.fitting_eq_core, QuotientModel.L_component,
    ⟨original_component_quotient⟩, original_binaryCore_fixed_not_central⟩
private theorem original_sup_core : L.subgroupOf P ⊔ E.subgroupOf P = ⊤ := by
  rw [← subgroupOf_sup L_le_P (show E ≤ P from le_sup_left)]
  have he : L ⊔ E = P :=
    le_antisymm (sup_le L_le_P le_sup_left)
      (sup_le le_sup_right ((show A ≤ L from le_sup_left).trans le_sup_left))
  rw [he, subgroupOf_self]

/-- Every literal Sylow two-subgroup supplements the original component. -/
theorem original_sylow_product (S : Sylow 2 P) :
    ∀ j : P, ∃ l ∈ L.subgroupOf P, ∃ r ∈ (S : Subgroup P), l * r = j := by
  let : (L.subgroupOf P).Normal := L_normal_in_P
  have hp : IsPGroup 2 (P ⧸ L.subgroupOf P) := isPGroup_quotient_of_sup_eq_top
    (L.subgroupOf P) (E.subgroupOf P)
    (E_isPGroup.comap_of_injective P.subtype P.subtype_injective) original_sup_core
  have ht : L.subgroupOf P ⊔ (S : Subgroup P) = ⊤ := by
    rw [sup_comm]
    exact S.sup_eq_top_of_quotient_isPGroup _ hp
  intro j
  exact mem_sup_of_normal_left.mp (ht.symm ▸ mem_top j)

/-- Taking the proper Sylow itself as H supplies the literal MS2(a) radical. -/
theorem original_sylow_radical (S : Sylow 2 P) :
    MSOddIndexRadical (S : Subgroup P) := by
  have hn : (S : Subgroup P) ≠ ⊤ := by
    intro ht
    have hp : IsPGroup 2 P := (ht ▸ S.isPGroup').of_equiv topEquiv
    have hSL := hp.of_surjective QuotientModel.projection QuotientModel.projection_surjective
    let : Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)
    let := Atlas.Comparisons.Exceptional.sl3Two_simple
    exact Group.IsPerfect.not_isNilpotent Matrix.PSL3Two.SL hSL.isNilpotent
  refine ⟨S, lt_top_iff_ne_top.mpr hn,
    Nat.not_even_iff_odd.mp (fun h => S.not_dvd_index (even_iff_two_dvd.mp h)), ?_⟩
  have he : pCore 2 S = ⊤ := top_unique
    (le_sSup ⟨inferInstance, S.isPGroup'.of_equiv topEquiv.symm⟩)
  rw [he, ← MonoidHom.range_eq_map, range_subtype]

/-- Every input field except MS3 is now certified on the original matrix
carrier. The remaining characteristic condition is owned by qt-rank-two-ms93;
this constructor does not assert that condition or the source classification. -/
noncomputable def originalInput_of_characteristic (S : Sylow 2 P)
    (hc : MSCharacteristicCondition (S : Subgroup P)) :
    BinaryMS.Input KnownSimple.IsKnownSimple (L.subgroupOf P) (S : Subgroup P) where
  sqtk := original_sqtk
  fitting := QuotientModel.fitting_eq_core
  product := original_sylow_product S
  component := QuotientModel.L_component
  radical := original_sylow_radical S
  characteristic := hc
  quotientEquiv := original_component_quotient

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
