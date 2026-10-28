module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Quotient
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.CComponent.CommutatorDichotomy
public import Mathlib.GroupTheory.IndexNormal

/-!
# The component construction following 13.3.14(d)

A nontrivial O₂(L₊*) centralizing F(H/O₂(H)) moves an ordinary component.
Lift it through O₂(H). The normal-or-index-two orbit bound and O²(L₊)=L₊
force normalization. The full component commutator dichotomy then proves
K=[K,L₊]; the quotient component identifies K/O₂(K) as quasisimple.

This is a conditional deduction, not reduction (d). Fitting centralization
remains to be proved in the assembly. The orbit bound is the precise part of
1.2.1(3) used here, whose source producer is qt-1-02. No component is assumed.
K is an intrinsic subgroup of H, so C-component membership and normalization
are relative to H, not to the ambient simple group.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
paragraph following Lemma 13.3.14(d), printed p.892, PDF p.909.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The range definition of star agrees with the image of the relative subgroup. -/
theorem star_eq_map (H A : Subgroup G) (hAH : A ≤ H) :
    star H A hAH = (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨inclusion hAH a, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

private theorem twoPerfect_le_of_index_two {D : Type*} [Group D]
    (A N : Subgroup D) (hA : IsPPerfect 2 A) (hi : N.index = 2) : A ≤ N := by
  let : N.Normal := N.normal_of_index_eq_two hi
  have hp : IsPGroup 2 (D ⧸ N) := IsPGroup.of_card (n := 1) (by
    change N.index = 2 ^ 1
    simpa using hi)
  exact (le_pResidual_of_isPPerfect A hA).trans (sInf_le ⟨inferInstance, hp⟩)

private theorem cComponent_commutator_eq_of_moved_image {D : Type*} [Group D] [Finite D]
    (K A : Subgroup D) (hK : K.IsCComponent)
    (hKn : A ≤ normalizer (K : Set D))
    (hKs : IsComponent (D ⧸ pCore 2 D) (K.map (QuotientGroup.mk' (pCore 2 D))))
    (hm : ⁅K.map (QuotientGroup.mk' (pCore 2 D)),
      A.map (QuotientGroup.mk' (pCore 2 D))⁆ ≠ ⊥) : ⁅K, A⁆ = K := by
  let q := QuotientGroup.mk' (pCore 2 D)
  have hqn : A.map q ≤ normalizer (K.map q : Set (D ⧸ pCore 2 D)) :=
    (map_mono hKn).trans (K.le_normalizer_map q)
  have hcomm := hKs.commutator_eq_self_of_normalizes hqn hm
  rcases hK.commutator_le_radical_or_eq_iSup_conjugates A with hr | he
  · let : Group.IsSolvable (⁅K, A⁆ : Subgroup D) :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hr) (inclusion_injective hr)
    let : Group.IsSolvable ((⁅K, A⁆ : Subgroup D).map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
    have hh : (⁅K, A⁆ : Subgroup D).map q = K.map q := by
      rw [map_commutator]
      exact hcomm
    have hs : Group.IsSolvable (K.map q) := hh ▸ inferInstance
    let := hKs.2
    let : Nontrivial (K.map q) := (nontrivial_iff_ne_bot _).mpr hKs.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable (K.map q) hs).elim
  · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hKn)
      ((le_iSup_conjugates K A).trans he.symm.le)

/-- Construct all component clauses after (d), retaining the literal star projection. -/
theorem exists_moved_component_of_fitting_centralization
    (H Lplus : Subgroup G) (hLH : Lplus ≤ H)
    (hperfect : IsPPerfect 2 Lplus)
    (horbits : ∀ K : Subgroup H, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set H)).index = 2)
    (hne : pCore 2 (star H Lplus hLH) ≠ ⊥)
    (hF : (star H Lplus hLH).pCoreIn 2 ≤
      centralizer (fittingSubgroup (Star H) : Set (Star H))) :
    ∃ K : Subgroup H, K.IsCComponent ∧
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)), (star H Lplus hLH).pCoreIn 2⁆ ≠ ⊥ ∧
      Lplus.subgroupOf H ≤ normalizer (K : Set H) ∧
      ⁅K, Lplus.subgroupOf H⁆ = K ∧ IsQuasisimple (K ⧸ pCore 2 K) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := (star H Lplus hLH).pCoreIn 2
  have hA : IsPGroup 2 A := pCore_isPGroup.map _
  have hAne : A ≠ ⊥ := by
    intro h
    apply hne
    exact (map_eq_bot_iff_of_injective _ (star H Lplus hLH).subtype_injective).mp h
  obtain ⟨J, hJ, hm⟩ := exists_component_moved_of_centralizes_fitting 2 A hA hAne
    (pCore_quotient_pCore_eq_bot 2) hF
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  obtain ⟨K, hK, hKJ⟩ := hJ.isCComponent.exists_map_quotient_eq (pCore 2 H)
  have hKs : IsComponent (Star H) (K.map q) := hKJ.symm ▸ hJ
  have hmove : ⁅K.map q, A⁆ ≠ ⊥ := hKJ.symm ▸ hm
  have hKn : Lplus.subgroupOf H ≤ normalizer (K : Set H) := by
    rcases horbits K hK with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact le_top
    · exact twoPerfect_le_of_index_two _ _
        (hperfect.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
          (subgroupOfEquivOfLe hLH).symm.surjective) hi
  have hmoveL : ⁅K.map q, (Lplus.subgroupOf H).map q⁆ ≠ ⊥ := by
    intro hz
    apply hmove
    apply bot_unique
    rw [← star_eq_map H Lplus hLH] at hz
    exact (commutator_mono le_rfl (map_subtype_le _)).trans hz.le
  have hcomm := cComponent_commutator_eq_of_moved_image K (Lplus.subgroupOf H)
    hK hKn hKs hmoveL
  let := hKs.2
  exact ⟨K, hK, hKs, hmove, hKn, hcomm,
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
