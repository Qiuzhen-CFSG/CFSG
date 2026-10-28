module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.SmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.TernaryCore
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallSylowQuotientSource
public import Theory.SpecificGroups.PSL3.TernaryAffineFour
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation
public import Theory.GroupTheory.SylowModelPullback
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The PSL₃(3) ternary affine source obstruction

The central involution supplied by the original source image theorem is used
to place the cyclic Sylow of the explicit E₉:C₄ subgroup inside the
selected quotient Sylow. The subgroup preimage then supplies the literal
small Sylow quotient obstruction.
Source: Aschbacher–Smith E.2.17, printed p.230.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree
open BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem source_ternary_small_automizer_false
    {κ : GroupClass} (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 3)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (_hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U)
    (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio
      (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hJ : J = pCore 2 H :=
    Structure.LinearThree.source_ternary_core_eq_twoCore T hP hs K hK hqK hgen hm
  obtain ⟨hcard,t,ht,htV⟩ := linear_source_image_involution
    T hP hs K hK hgen (by decide : Nat.Prime 3) (by decide : Odd 3) hm V hVT hvn hout hres
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let Q := H ⧸ J
  have hWcard : Nat.card W = 2 := hcard
  have hqT : (S : Subgroup Q) = (T : Subgroup H).map q := rfl
  have hqT_sylow : Sylow 2 Q := S
  have htS : (t : Q) ∈ (S : Subgroup Q) := by
    exact (show W ≤ (S : Subgroup Q) from map_mono hVT) (htV)
  obtain ⟨F, hF, hfin, hFc, ⟨e⟩⟩ := hm
  obtain ⟨i0, hi0, hic⟩ := Matrix.PSL3.TernaryAffineFour.exists_embedding
    hFc (e t) ((e.orderOf_eq t).trans ht)
  let i : Matrix.PSL3.TernaryAffineFour.Local →* Q :=
    (K.map q).subtype.comp (e.symm.toMonoidHom.comp i0)
  have hi : Function.Injective i := (K.map q).subtype_injective.comp
    (e.symm.injective.comp hi0)
  have hicQ : i Matrix.PSL3.TernaryAffineFour.central = (t : Q) := by
    change (e.symm (i0 Matrix.PSL3.TernaryAffineFour.central)).val = t.val
    rw [hic, e.symm_apply_apply]
  have htQ : orderOf (t : Q) = 2 :=
    (orderOf_injective (K.map q).subtype (K.map q).subtype_injective t).trans ht
  have hztW : zpowers (t : Q) ≤ W := zpowers_le.mpr htV
  have hztcard : Nat.card (zpowers (t : Q)) = 2 := by
    rw [Nat.card_zpowers, htQ]
  have hW_eq : zpowers (t : Q) = W :=
    Subgroup.eq_of_le_of_card_ge hztW (hWcard ▸ hztcard.ge)
  let M := ChapterB.minimalParabolicMax T hP
  let Dq := K.map q
  have hiD := Structure.source_normal_simple_image T hP hs K hK hgen
  let : Dq.Normal := hiD.2.2.1
  let : IsSimpleGroup Dq := hiD.1
  let hmin := (Structure.source_star_minimal_core_free T hP).1
  have hO : pCore 2 Q = ⊥ := bot_unique
    ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hMW : M.map q ≤ normalizer (W : Set Q) := by
    exact (map_mono (source_maximal_normalizes_of_residual_centralizes T hP V hVT hvn hres)).trans
      (le_normalizer_map q)
  have hMW' : ChapterB.minimalParabolicMax S hmin ≤ normalizer (W : Set Q) := by
    rw [hmax]
    exact hMW
  have hSW : (S : Subgroup Q) ≤ normalizer (W : Set Q) :=
    (ChapterB.minimalParabolicMax_spec S hmin).2.trans hMW'
  have hSC : (S : Subgroup Q) ≤ centralizer ({(t : Q)} : Set Q) := by
    rw [← normalizer_zpowers_eq_centralizer_of_order_two (t : Q) htQ, hW_eq]
    exact hSW
  let Cq : Subgroup Q := centralizer ({(t : Q)} : Set Q)
  have hSC' : (S : Subgroup Q) ≤ normalizer (Cq : Set Q) :=
    hSC.trans Cq.le_normalizer
  let W0 : Subgroup Q := (Matrix.PSL3.TernaryAffineFour.sylow :
    Subgroup Matrix.PSL3.TernaryAffineFour.Local).map i
  have hW0C : W0 ≤ Cq := by
    rw [map_le_iff_le_comap]
    intro z hz
    apply mem_centralizer_singleton_iff.mpr
    have hz' := Matrix.PSL3.TernaryAffineFour.sylow_centralizes hz
    rw [← hicQ]
    simpa only [map_mul] using congrArg i (mem_centralizer_singleton_iff.mp hz')
  have hW0p : IsPGroup 2 W0 :=
    Matrix.PSL3.TernaryAffineFour.sylow.isPGroup'.map i
  obtain ⟨c, hcC, hcW⟩ := IsPGroup.exists_conj_le_sylow_of_normalized
    S Cq W0 hSC' hW0p hW0C
  let j : Matrix.PSL3.TernaryAffineFour.Local →* Q :=
    (MulAut.conj c).toMonoidHom.comp i
  have hj : Function.Injective j := (MulAut.conj c).injective.comp hi
  have hjc : j Matrix.PSL3.TernaryAffineFour.central = (t : Q) := by
    calc
      c * i Matrix.PSL3.TernaryAffineFour.central * c⁻¹ =
          c * (t : Q) * c⁻¹ := by rw [hicQ]
      _ = (t : Q) * c * c⁻¹ := by rw [mem_centralizer_singleton_iff.mp hcC]
      _ = (t : Q) := by simp
  let R : Subgroup Q := j.range
  have hW_R : W ≤ R := by
    rw [← hW_eq, zpowers_le]
    exact ⟨Matrix.PSL3.TernaryAffineFour.central, hjc⟩
  have hAlign :
      ((Matrix.PSL3.TernaryAffineFour.sylow : Subgroup Matrix.PSL3.TernaryAffineFour.Local).map j)
        ≤ (S : Subgroup Q) := by
    simpa only [j, W0, Subgroup.map_map] using hcW
  have hq2 : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk', hJ]
    exact pCore_isPGroup
  obtain ⟨g,hg,hgker,hinter,S0,hS0T,hS0g⟩ :=
    Sylow.exists_model_pullback q (QuotientGroup.mk'_surjective J) hq2 j hj T
      Matrix.PSL3.TernaryAffineFour.sylow hAlign
  let L : Subgroup H := j.range.comap q
  have hVL : V ≤ L := by
    change V ≤ j.range.comap q
    apply (map_le_iff_le_comap).mp
    simpa only [W, R] using hW_R
  have hLn : pCore 2 H ≤ normalizer (L : Set H) := by
    have hqkerL : q.ker ≤ L := j.range.ker_le_comap q
    rw [QuotientGroup.ker_mk', hJ] at hqkerL
    exact hqkerL.trans L.le_normalizer
  have hP0 : IsCoatom ((S0 : Subgroup L).map g) := by
    rw [hS0g]
    exact Matrix.PSL3.TernaryAffineFour.sylow_isCoatom
  have hPn0 : ¬((S0 : Subgroup L).map g).Normal := by
    rw [hS0g]
    exact Matrix.PSL3.TernaryAffineFour.sylow_not_normal
  have hA0 : Group.IsSolvable Matrix.PSL3.TernaryAffineFour.Local :=
    Matrix.PSL3.TernaryAffineFour.solvable
  have hO0 : pCore 2 Matrix.PSL3.TernaryAffineFour.Local = ⊥ :=
    Matrix.PSL3.TernaryAffineFour.twoCore
  have h9 : Nat.card (pResidual 2 Matrix.PSL3.TernaryAffineFour.Local) = 9 :=
    Matrix.PSL3.TernaryAffineFour.card_residual
  have hout0 : ¬ V.subgroupOf L ≤ g.ker := by
    intro hvk
    apply hout
    intro v hv
    have hx : (⟨v,hVL hv⟩ : L) ∈ g.ker := hvk hv
    rw [hgker] at hx
    change v ∈ q.ker at hx
    simpa only [q, QuotientGroup.ker_mk'] using hx
  have hg2 : IsPGroup 2 g.ker := by
    rw [hgker]
    exact hq2.comap_subtype
  exact source_subgroup_small_sylow_quotient_false hH T hVT hvn hfit hV hTU hU
    f hf hk hD hratio L hVL hLn S0 hS0T g hg hg2 hA0 hO0 hP0 hPn0 hout0 h9

end CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree
