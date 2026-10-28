module

public import Stellmacher.SectionFour.PartnerCoreIdentification
public import Stellmacher.CharacteristicTwoCoreOvergroup

/-!
# The partner core is the core of M in Stellmacher (4.6)

For the actual subgroup `M = mSubgroup S` and the starred critical partner
from the Baumann configuration, `O₂(Pstar) = O₂(M)`. The finite ambient
group, Section Four hypotheses, actual starred membership, and all inputs
of the partner-core identification are retained.

The proved identification `O₂(Pstar) = V` makes the partner core elementary
abelian. Since `Pstar ≤ M` and both contain the fixed Sylow, `O₂(M) ≤ S ≤
Pstar`; restricting its normality gives `O₂(M) ≤ O₂(Pstar)`. Thus the abelian
partner core centralizes `O₂(M)`. Characteristic two of `M` gives the reverse
inclusion. To obtain that characteristic-two hypothesis, (4.1) makes
`O₂(M)` nontrivial, so its normalizer `N` is a 2-local subgroup containing
`S`. The standing local hypotheses give characteristic two of `N`, and
`O₂(N) ≤ S ≤ M` permits core-overgroup inheritance.

Source: `refs/latex/stellmacher-n-group.tex`, proof of (4.6), journal page 26,
the implication from the partner-core identification to
`O₂(Pstar) = O₂(M)`. This argument needs no normality of `Pstar` in `M`.
-/

open scoped Pointwise

namespace Stellmacher.SectionFour

private theorem core_le_fixed_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (L : Subgroup G) (hSL : (S : Subgroup G) ≤ L) :
    twoCoreAmbient L ≤ (S : Subgroup G) := by
  let T : Sylow 2 L := S.subtype hSL
  have hT : (T : Subgroup L).map L.subtype = (S : Subgroup G) :=
    Subgroup.map_subgroupOf_eq_of_le hSL
  rw [← hT]
  exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal T)

private theorem subgroup_le_normalizer_core
    {G : Type*} [Group G] (L : Subgroup G) :
    L ≤ Subgroup.normalizer (twoCoreAmbient L : Set G) := by
  have hn : ((twoCoreAmbient L).subgroupOf L).Normal := by
    change (((pCore 2 L).map L.subtype).subgroupOf L).Normal
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show twoCoreAmbient L ≤ L from Subgroup.map_subtype_le _)).mp hn

/-- The actual starred partner and `M` have the same two-core. -/
public theorem partner_core_eq_m_core
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (P Pstar E : Subgroup G)
    (hstar : Pstar ∈ SectionThree.PStarSet (mSubgroup S) (S : Subgroup G))
    (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    twoCoreAmbient Pstar = twoCoreAmbient (mSubgroup S) := by
  let M := mSubgroup S
  have hPM : Pstar ≤ M := hstar.1.1.1
  have hSP : (S : Subgroup G) ≤ Pstar := by
    obtain ⟨T,hT⟩ := hstar.1.1.2.1
    exact hT ▸ Subgroup.map_subtype_le _
  have hSM : (S : Subgroup G) ≤ M := hSP.trans hPM
  let N := Subgroup.normalizer (twoCoreAmbient M : Set G)
  have hMN : M ≤ N := subgroup_le_normalizer_core M
  have hSN : (S : Subgroup G) ≤ N := hSM.trans hMN
  have hNlocal : IsTwoLocal N :=
    ⟨twoCoreAmbient M, (lemma_four_one S h).part_b,
      (pCore_isPGroup (p := 2) (G := M)).map M.subtype, rfl⟩
  have hNchar : IsCharacteristicTwoType N :=
    (h.local_solvable_characteristicTwo N hNlocal hSN).2
  have hMchar : IsCharacteristicTwoType M :=
    characteristicTwo_of_contains_core_in N M hNchar hMN
      ((core_le_fixed_sylow S N hSN).trans hSM)
  have hQMP : twoCoreAmbient M ≤ Pstar :=
    (core_le_fixed_sylow S M hSM).trans hSP
  have hQMnormalP : ((twoCoreAmbient M).subgroupOf Pstar).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMP).mpr
      (hPM.trans (subgroup_le_normalizer_core M))
  have hQMtwo : IsPGroup 2 ((twoCoreAmbient M).subgroupOf Pstar) :=
    ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQMP).symm
  have hQMQP : twoCoreAmbient M ≤ twoCoreAmbient Pstar := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQMP]
    exact Subgroup.map_mono (le_sSup ⟨hQMnormalP,hQMtwo⟩)
  have hQPelem : IsElementaryAbelian 2 (pCore 2 Pstar) := by
    rw [partner_core_eq_v S h.even_order P Pstar E hpair hPC hEP hsolv hchar hE hSyl]
    obtain ⟨SP,hsec,_hSP,hV⟩ :=
      original_partner_sectionTwo_data S h.even_order P Pstar E
        hpair hPC hEP hsolv hchar hE hSyl
    rw [← hV]
    exact (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec SP).2
  let _ : IsElementaryAbelian 2 (twoCoreAmbient Pstar) := hQPelem.map Pstar.subtype
  have hcent : twoCoreAmbient Pstar ≤ Subgroup.centralizer
      (twoCoreAmbient Pstar : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply le_antisymm ?_ hQMQP
  intro x hx
  have hxP : x ∈ Pstar := Subgroup.map_subtype_le _ hx
  let xM : M := ⟨x,hPM hxP⟩
  have hxcent : xM ∈ Subgroup.centralizer (pCore 2 M : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcent hx) y
      (hQMQP (Subgroup.mem_map_of_mem M.subtype hy))
  exact Subgroup.mem_map_of_mem M.subtype (hMchar hxcent)

end Stellmacher.SectionFour
