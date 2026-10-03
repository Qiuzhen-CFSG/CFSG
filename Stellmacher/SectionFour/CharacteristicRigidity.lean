module

public import Stellmacher.SectionFour.LemmaFourThree
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# Characteristic rigidity from a critical pair

Let `(P,Pstar)` be a Section Four critical pair, and suppose `B ≤ S` is
normalized by `P`. If `B ≤ L` and `Pstar ≤ L ⋁ S`, no nontrivial
characteristic subgroup of `B` is normal in `L`. This is the rigidity
step for the Baumann subgroup in Stellmacher (4.6).

Characteristicity transfers normalization from `B` to its characteristic
subgroup, hence gives normalization by `P` and `S ≤ P`. Normality in
`L` then gives normalization by `Pstar`. The subgroup is a normal
2-subgroup of the critical join, whose 2-core is trivial.

Source: `refs/latex/stellmacher-n-group.tex`, second paragraph of (4.6).
-/

namespace Stellmacher.SectionFour

/-- A characteristic subgroup of the shared 2-subgroup cannot be normal
in a subgroup generating the critical partner with the fixed Sylow. -/
public theorem critical_pair_characteristic_rigidity
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (P Pstar B L : Subgroup G)
    (hpair : (P, Pstar) ∈ Lambda S) (hBS : B ≤ (S : Subgroup G))
    (hPB : P ≤ Subgroup.normalizer (B : Set G)) (hBL : B ≤ L)
    (hgen : Pstar ≤ L ⊔ (S : Subgroup G))
    (K : Subgroup B) (hKchar : K.Characteristic)
    (hKN : ((K.map B.subtype).subgroupOf L).Normal) : K = ⊥ := by
  let H : Subgroup G := K.map B.subtype
  have hHB : H ≤ B := Subgroup.map_subtype_le _
  have hHS : H ≤ (S : Subgroup G) := hHB.trans hBS
  have hHL : H ≤ L := hHB.trans hBL
  have hSP : (S : Subgroup G) ≤ P := by
    obtain ⟨T, hT⟩ := hpair.1.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hPH : P ≤ Subgroup.normalizer (H : Set G) := by
    let _ : K.Characteristic := hKchar
    exact hPB.trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic B K)
  have hLH : L ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHL).mp hKN
  have hPstarH : Pstar ≤ Subgroup.normalizer (H : Set G) :=
    hgen.trans (sup_le hLH (hSP.trans hPH))
  have hHJ : H ≤ P ⊔ Pstar := hHS.trans (hSP.trans le_sup_left)
  have hHN : (H.subgroupOf (P ⊔ Pstar)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHJ).mpr (sup_le hPH hPstarH)
  have hHp : IsPGroup 2 H := S.isPGroup'.to_le hHS
  have hHpJ : IsPGroup 2 (H.subgroupOf (P ⊔ Pstar)) :=
    hHp.comap_of_injective (P ⊔ Pstar).subtype (P ⊔ Pstar).subtype_injective
  have hHcore : H ≤ twoCoreAmbient (P ⊔ Pstar) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hHJ]
    exact Subgroup.map_mono (le_sSup ⟨hHN, hHpJ⟩)
  have hHbot : H = ⊥ := le_bot_iff.mp (hHcore.trans_eq hpair.2.2)
  exact (Subgroup.map_eq_bot_iff_of_injective K B.subtype_injective).mp hHbot

end Stellmacher.SectionFour
