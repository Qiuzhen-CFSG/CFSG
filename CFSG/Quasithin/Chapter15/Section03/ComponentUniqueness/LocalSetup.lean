module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The hypotheses of 1.1.5 in the component argument

For an outside overgroup `I`, enlarge `I` to a maximal two-local `H`.
The local Sylow conclusion 15.3.11(1) gives `T ∩ H = S`. The normal
two-subgroup `O₂(H)` therefore lies in `S`, and hence in `O₂(I ∩ M_c)`.
Maximality identifies `N_G(O₂(H))` with `H`; this bounds the required
core centralizer by `T ∩ H = S ≤ I`.

This proves 15.3.33(2) from the explicit local Sylow and central-involution
inputs. It does not assume a core-centralizer bound or any component
classification. Source: Aschbacher--Smith, combined manuscript (1 March
2004), printed p.1134, with Lemma 1.1.5 on p.501.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The exact local Sylow input 15.3.11(1), with the subgroup `S`
embedded in the ambient group. -/
@[expose] def OutsideSylowControl (Yplus S M : Subgroup G) : Prop :=
  ∀ I ∈ outsideFamily Yplus S M,
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S

/-- The centralizer inclusion required in 1.1.5 follows from the common
Sylow subgroup of all outside overgroups, rather than being an extra input. -/
theorem component_core_centralizer_le
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hST : S ≤ (T : Subgroup G)) (hTMc : (T : Subgroup G) ≤ Mc) :
    Mc.pCoreIn 2 ⊓ centralizer ((I ⊓ Mc).pCoreIn 2 : Set G) ≤ I := by
  have hcoreI : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1.1
    simp only [pCoreIn, he, Subgroup.map_bot]
  obtain ⟨H, hH, hIH⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcoreI
  have hHout : H ∈ outsideFamily Yplus S M :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hH.1, hI.1.2.trans hIH⟩,
      fun hHM => hI.2 (hIH.trans hHM)⟩
  obtain ⟨P, hP⟩ := hSylow H hHout
  have hSI : S ≤ I := le_sup_right.trans hI.1.2
  have hHT : (T : Subgroup G) ⊓ H = S := by
    rw [inf_eq_sylow_map P T.isPGroup' (hP ▸ hST), hP]
  have hcoreHS : H.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow H P
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hNH : normalizer (H.pCoreIn 2 : Set G) ≤ H :=
    hH.2 ⟨H.pCoreIn 2, hHout.1.1, isPGroup_pCoreIn 2 H, rfl⟩ hHN
  have hcore : H.pCoreIn 2 ≤ (I ⊓ Mc).pCoreIn 2 :=
    le_pCoreIn_inf (isPGroup_pCoreIn 2 H) (hcoreHS.trans hSI)
      (hcoreHS.trans (hST.trans hTMc)) (hIH.trans hHN)
  have hMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow Mc (T.subtype hTMc)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTMc] using hh
  calc
    Mc.pCoreIn 2 ⊓ centralizer ((I ⊓ Mc).pCoreIn 2 : Set G)
        ≤ (T : Subgroup G) ⊓ H :=
      inf_le_inf hMcT ((centralizer_le hcore).trans
        ((Subgroup.centralizer_le_normalizer _).trans hNH))
    _ = S := hHT
    _ ≤ I := hSI

/-- Source 15.3.33(2). The input `hMc` is `M_c ∈ H_e(T)` and
`hCz` is the centralizer conclusion of 15.3.4. No conclusion of 1.1.5
is included among the assumptions. -/
theorem lemma_15_3_33_2
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hST : S ≤ (T : Subgroup G))
    (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S ∧
      Chapter1.Lemma115Hypotheses I P Mc z := by
  obtain ⟨P, hP⟩ := hSylow I hI
  refine ⟨P, hP, hI.1.1, ?_,
    component_core_centralizer_le T hI hSylow hST hMc.2.2,
    hz, hP.symm ▸ hzS, ?_, hCz.le⟩
  · exact ⟨hMc.1, hMc.2.1, hP.symm ▸ hST.trans hMc.2.2⟩
  · intro s hs
    exact hzcentral s (hST (hP ▸ hs))

end CFSG.Quasithin.Chapter15.Section03
