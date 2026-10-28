module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# The Sylow subgroup in the actual source group LR

The component of J(I) is a C-component of I. Thus the Sylow subgroup S of I
meets L in a Sylow subgroup of L. Joining that intersection with R constructs
a Sylow subgroup of LR: its ambient image is S ∩ LR. Only R normalizes L
in this argument; normalization by the whole S is not required.

This comparison does not identify the image with S and does not bound the
center of the smaller Sylow subgroup. The additional ambient action needed
to exclude C.1.34(4) remains a separate source obligation.

Source: Aschbacher–Smith, 15.3.11(1), 15.3.12(1), 15.3.17 and 15.3.23,
printed pp.1123–1128, and C.1.34, printed pp.136–137.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Promote the relative C-component of J(I) to the actual outside group I. -/
theorem component_in_overgroup (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I) :
    (c.L.subgroupOf I).IsCComponent := by
  let J := Stellmacher.elementaryAbelianMaxJ I
  have hJI : J ≤ I := sSup_le fun A hA => hA.1
  have hn : I ≤ normalizer (J : Set G) := by
    intro i hi
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ I).map (MulAut.conj i).toMonoidHom = J
    rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj i) I]
    exact congrArg Stellmacher.elementaryAbelianMaxJ
      (show I.map (MulAut.conj i).toMonoidHom = I from
        mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer hi))
  have hJn : (J.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  have hc : ((c.L.subgroupOf I).subgroupOf (J.subgroupOf I)).IsCComponent := by
    let e := subgroupOfEquivOfLe hJI
    have h := c.component.map_equiv e.symm
    convert h using 1
    ext x
    simp only [mem_subgroupOf, mem_map_equiv, MulEquiv.symm_symm]
    rfl
  exact (IsCComponent.subgroupOf_iff hJn.isSubnormal
    (show c.L.subgroupOf I ≤ J.subgroupOf I from fun _ hx => c.le_thompson hx)).mp hc

omit [Finite G] in
/-- The same component in LR, with both ambient inclusions justified. -/
theorem component_in_source (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hI : I ∈ d.Hplus) :
    (c.L.subgroupOf (c.L ⊔ d.R)).IsCComponent := by
  let H := c.L ⊔ d.R
  have hHI : H ≤ I := sup_le (component_le c)
    (((d.Yplus ⊔ d.S).pCoreIn_le 2).trans hI.1.2)
  have hLH : c.L.subgroupOf I ≤ H.subgroupOf I :=
    fun _ hx => (le_sup_left : c.L ≤ H) hx
  have hc := ((component_in_overgroup d c).subgroupOf hLH).map_equiv
    (subgroupOfEquivOfLe hHI)
  convert hc using 1
  ext x
  simp only [mem_subgroupOf, mem_map_equiv]
  rfl

omit [Finite G] in
/-- The relative normality used by C.1.34 follows from R-normalization alone. -/
theorem component_normal_in_source (d : LocalData G) (L : Subgroup G)
    (hRL : d.R ≤ normalizer (L : Set G)) :
    (L.subgroupOf (L ⊔ d.R)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hRL)

private theorem sylow_in_join (L R S : Subgroup G) (hS : IsPGroup 2 S)
    (hRS : R ≤ S) (hRL : R ≤ normalizer (L : Set G))
    (Q : Sylow 2 L) (hQ : (Q : Subgroup L) = S.subgroupOf L) :
    ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = S.subgroupOf (L ⊔ R) := by
  let U := (S ⊓ L) ⊔ R
  have hUS : U ≤ S := sup_le inf_le_left hRS
  have hUL : U ≤ normalizer (L : Set G) :=
    sup_le (inf_le_right.trans L.le_normalizer) hRL
  have hjoin : L ⊔ U = L ⊔ R := by
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hQU : (Q : Subgroup L).map L.subtype ≤ U := by
    rw [hQ]
    rintro x ⟨l, hl, rfl⟩
    exact mem_sup_left ⟨hl, l.property⟩
  have hex := (hS.to_le hUS).exists_sylow_sup_of_coprime_index
    L U hUL (Q : Subgroup L) Q.not_dvd_index hQU
  rw [hjoin] at hex
  obtain ⟨P, hP⟩ := hex
  refine ⟨P, ?_⟩
  apply Eq.symm
  apply P.is_maximal'
  · exact hS.comap_of_injective (L ⊔ R : Subgroup G).subtype
      (L ⊔ R : Subgroup G).subtype_injective
  · intro p hp
    exact hUS (hP ▸ mem_map_of_mem (L ⊔ R : Subgroup G).subtype hp)

/-- Restrict the given Sylow subgroup of I to the subnormal component L. -/
theorem component_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (T : Sylow 2 I)
    (hT : (T : Subgroup I).map I.subtype = d.S) :
    ∃ Q : Sylow 2 c.L, (Q : Subgroup c.L) = d.S.subgroupOf c.L := by
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_subnormal
    (c.L.subgroupOf I) (component_in_overgroup d c).subnormal
  let e := subgroupOfEquivOfLe (component_le c)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (Q : Subgroup (c.L.subgroupOf I)).map e.toMonoidHom = _
  rw [hQ]
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact hT ▸ mem_map_of_mem I.subtype hl
  · intro hx
    have hx' : (x : G) ∈ (T : Subgroup I).map I.subtype := hT ▸ hx
    obtain ⟨i, hi, hix⟩ := hx'
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have he : i = (e.symm x : I) := Subtype.ext hix
    change (e.symm x : I) ∈ (T : Subgroup I)
    exact he ▸ hi

/-- The local Sylow contains R and embeds as exactly S ∩ LR. -/
theorem local_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (T : Sylow 2 I)
    (hT : (T : Subgroup I).map I.subtype = d.S)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hRL : d.R ≤ normalizer (c.L : Set G)) :
    ∃ P : Sylow 2 (c.L ⊔ d.R : Subgroup G),
      (P : Subgroup (c.L ⊔ d.R : Subgroup G)) = d.S.subgroupOf (c.L ⊔ d.R) ∧
      d.R.subgroupOf (c.L ⊔ d.R) ≤ (P : Subgroup (c.L ⊔ d.R : Subgroup G)) ∧
      (P : Subgroup (c.L ⊔ d.R : Subgroup G)).map (c.L ⊔ d.R : Subgroup G).subtype =
        d.S ⊓ (c.L ⊔ d.R) := by
  have hRS : d.R ≤ d.S := le_inf (hR.le.trans inf_le_left)
    ((hR.le.trans inf_le_right).trans
      ((centralizer_le (d.action.plane_le 1)).trans (Subgroup.centralizer_le_normalizer _)))
  obtain ⟨Q, hQ⟩ := component_sylow d c T hT
  obtain ⟨P, hP⟩ := sylow_in_join c.L d.R d.S
    (d.T.isPGroup'.to_le inf_le_left) hRS hRL Q hQ
  refine ⟨P, hP, ?_, ?_⟩
  · rw [hP]
    exact fun _ hx => hRS hx
  · rw [hP]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · rintro ⟨hS, hH⟩
      exact ⟨⟨x, hH⟩, hS, rfl⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
end
