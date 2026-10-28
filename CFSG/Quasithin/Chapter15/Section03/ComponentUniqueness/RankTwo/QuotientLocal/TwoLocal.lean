module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup

/-!
# A two-local witness in the component quotient

The witness in 15.3.41(2) is the embedded two-core of M_I⁺. The standing
natural module V lies in S and is normalized by M, so V ≤ O₂(M_I).
Maximal two-locality of M gives N_G(V)=M. Thus C_I(O₂(M_I)) lies in M_I,
and characteristic two of M_I from 15.3.11(7) makes this core
self-centralizing in I. Its normalizer has characteristic two; applying
15.3.25 to that actual overgroup forces its normalizer to be M_I.

The kernel C_I(L) is a normal two-subgroup by the transport module.
The Sylow conclusion 15.3.11(1) puts it in S, hence in O₂(M_I).
Consequently the full normalizer equality passes to I/C_I(L), and the
image core is exactly O₂(M_I⁺). This image is nontrivial: otherwise V
centralizes L, forcing L ≤ C_G(V) ≤ M, contrary to 15.3.33(3).

The final theorem derives the module properties from the actual natural
orthogonal action in LocalData. Its remaining inputs are the standing
maximal two-local hypothesis, 15.3.11(1),(7), 15.3.25, the component facts
15.3.33(3), and I=LS from the minimality step preceding 15.3.41.
Characteristic two of M_I⁺ is not required for this argument; the other
clauses of LocalConfiguration remain with the quotient assembly owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11, 15.3.25, 15.3.33 and 15.3.41(2), printed pp.1123--1124,
1130, 1134 and 1138.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem intersection_core_selfCentralizing
    {I M V : Subgroup G} (hVI : V ≤ I) (hVM : V ≤ M)
    (hVp : IsPGroup 2 V) (hMV : M ≤ normalizer (V : Set G))
    (hCV : centralizer (V : Set G) ≤ M)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G)) :
    centralizer ((M.subgroupOf I).pCoreIn 2 : Set I) ≤ (M.subgroupOf I).pCoreIn 2 := by
  let H := M.subgroupOf I
  have hV : V.subgroupOf I ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hVp.comap_subtype (comap_mono hVM) (by
      rw [← subgroupOf_normalizer_eq hVI]
      exact comap_mono hMV)
  have hCH : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    have hc : centralizer (pCore 2 (M ⊓ I : Subgroup G) : Set (M ⊓ I : Subgroup G)) ≤
        pCore 2 (M ⊓ I : Subgroup G) := by
      rw [← hF]
      exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    have he := (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (show M ⊓ I ≤ I from inf_le_right))).mpr hc
    rwa [inf_subgroupOf_right] at he
  intro x hx
  have hxH : x ∈ H := by
    apply hCV
    intro v hv
    exact congrArg Subtype.val (hx ⟨v, hVI hv⟩ (hV hv))
  exact mem_map_of_mem H.subtype (hCH (show (⟨x, hxH⟩ : H) ∈ centralizer (pCore 2 H : Set H) from by
    intro y hy
    exact Subtype.ext (hx y (mem_map_of_mem H.subtype hy))))

/-- The core normalizer in I follows from 15.3.25 applied to that actual overgroup. -/
private theorem intersection_twoCore_normalizer
    {I M V Y S : Subgroup G}
    (hVI : V ≤ I) (hVM : V ≤ M) (hVp : IsPGroup 2 V)
    (hMV : M ≤ normalizer (V : Set G)) (hCV : centralizer (V : Set G) ≤ M)
    (hYM : Y ≤ M) (hSM : S ≤ M) (hYSI : Y ⊔ S ≤ I) (hVne : V ≠ ⊥)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G))
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A) :
    normalizer ((M.subgroupOf I).pCoreIn 2 : Set I) = M.subgroupOf I := by
  let H := M.subgroupOf I
  let D := H.pCoreIn 2
  let N := normalizer (D : Set I)
  let A := N.map I.subtype
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hDne : D ≠ ⊥ := by
    have hV : V.subgroupOf I ≤ D :=
      le_pCoreIn_of_normalizes hVp.comap_subtype (comap_mono hVM) (by
        rw [← subgroupOf_normalizer_eq hVI]
        exact comap_mono hMV)
    intro he
    have hvbot : V.subgroupOf I = ⊥ := bot_unique (he ▸ hV)
    apply hVne
    rw [← map_subgroupOf_eq_of_le hVI, hvbot, Subgroup.map_bot]
  have hCN : centralizer (pCore 2 N : Set N) ≤ pCore 2 N :=
    centralizer_pCore_le_of_normalized 2 D N (isPGroup_pCoreIn 2 H)
      D.le_normalizer le_rfl (intersection_core_selfCentralizing hVI hVM hVp hMV hCV hF)
  have hCA : centralizer (pCore 2 A : Set A) ≤ pCore 2 A :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2
      (Subgroup.equivMapOfInjective N I.subtype I.subtype_injective)).mp hCN
  have hFA : generalizedFitting A = pCore 2 A :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hCA
  have hDN : D ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) D.le_normalizer le_rfl
  have hAcore : A.pCoreIn 2 ≠ ⊥ := by
    have hmap : (N.pCoreIn 2).map I.subtype = A.pCoreIn 2 :=
      map_pCoreIn_of_ker_isPGroup I.subtype
        (IsPGroup.ker_isPGroup_of_injective I.subtype_injective) N
    intro hz
    have hd : D.map I.subtype = ⊥ := bot_unique ((map_mono hDN).trans (hmap.trans hz).le)
    exact hDne ((D.map_eq_bot_iff_of_injective I.subtype_injective).mp hd)
  have hYA : Y ⊔ S ≤ A := by
    intro x hx
    exact ⟨⟨x, hYSI hx⟩, hHN ((sup_le hYM hSM) hx), rfl⟩
  have hAM : A ≤ M := by
    by_contra hn
    exact h25 A ⟨⟨hAcore, hYA⟩, hn⟩ hFA
  exact le_antisymm (fun x hx => hAM ⟨x, hx, rfl⟩) hHN

/-- The image of O₂(M_I) is the nontrivial two-core of M_I⁺ and its full
normalizer is M_I⁺. The module assumptions are consequences of the standing
local setup, as discharged by `componentImage_isTwoLocal` below. -/
theorem componentImage_twoCore_witness
    {I L M V Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (hLI : L ≤ I) (hIeq : I = L ⊔ S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hZ : IsPGroup 2 (center L)) (hLM : ¬ L ≤ M)
    (hVS : V ≤ S) (hVM : V ≤ M) (hVp : IsPGroup 2 V)
    (hMV : M ≤ normalizer (V : Set G)) (hCV : centralizer (V : Set G) ≤ M)
    (hYM : Y ≤ M) (hSM : S ≤ M) (hYI : Y ≤ I)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G))
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A) :
    (componentImage I L M).pCoreIn 2 ≠ ⊥ ∧
      normalizer ((componentImage I L M).pCoreIn 2 : Set (ComponentQuotient I L)) =
        componentImage I L M := by
  let q := centralizerQuotientMap (L.subgroupOf I)
  let H := M.subgroupOf I
  let D := H.pCoreIn 2
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hSp : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hk : IsPGroup 2 q.ker := component_kernel_isTwoGroup hLI hIeq hSp hZ
  have hSI : S ≤ I := hIeq ▸ le_sup_right
  have hVI : V ≤ I := hVS.trans hSI
  have hVD : V.subgroupOf I ≤ D :=
    le_pCoreIn_of_normalizes hVp.comap_subtype (comap_mono hVM) (by
      rw [← subgroupOf_normalizer_eq hVI]
      exact comap_mono hMV)
  have hVk : ¬ V.subgroupOf I ≤ q.ker := by
    intro h
    have hv : V ≤ centralizer (L : Set G) := by
      intro v hv l hl
      have hh := h (show (⟨v, hVI hv⟩ : I) ∈ V.subgroupOf I from hv)
      rw [show q.ker = (centralizer (L : Set G)).subgroupOf I from component_kernel_eq I L hLI] at hh
      exact hh l hl
    exact hLM ((le_centralizer_iff.mp hv).trans hCV)
  have hVne : V ≠ ⊥ := by
    intro he
    apply hVk
    simp only [he, bot_subgroupOf, bot_le]
  have hN := intersection_twoCore_normalizer hVI hVM hVp hMV hCV hYM hSM
    (sup_le hYI hSI) hVne hF h25
  have hkerH : q.ker ≤ H := by
    intro x hx
    apply hSM
    rw [← hP]
    exact mem_map_of_mem I.subtype (hk.le_sylow_of_normal P hx)
  have hkerD : q.ker ≤ D :=
    le_pCoreIn_of_normalizes hk hkerH (by rw [normalizer_eq_top]; exact le_top)
  have himage : D.map q = (componentImage I L M).pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup q hk H
  refine ⟨?_, ?_⟩
  · rw [← himage]
    intro he
    exact hVk (hVD.trans ((D.map_eq_bot_iff).mp he))
  · apply Subgroup.comap_injective hq
    rw [comap_normalizer_eq_of_surjective _ hq, ← himage,
      comap_map_eq_self hkerD, hN]
    exact (comap_map_eq_self hkerH).symm

/-- The two-local clause of 15.3.41(2) from the genuine standing local choices.
Here `hF` is precisely 15.3.11(7), while `h25` is applied to the actual
normalizer overgroup. No two-locality or normalizer equality in the component
quotient is assumed. -/
theorem componentImage_isTwoLocal
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G} [(L.subgroupOf I).Normal]
    (hM : IsMaximalTwoLocal d.M) (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hIeq : I = L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hZ : IsPGroup 2 (center L)) (hLM : ¬ L ≤ d.M)
    (hF : generalizedFitting (d.MI I) = pCore 2 (d.MI I))
    (h25 : ∀ A ∈ d.Hplus, generalizedFitting A ≠ pCore 2 A) :
    IsTwoLocal (componentImage I L d.M) := by
  have hVM : d.V ≤ d.M := localModule_le d.T d.sylow_le
  have hVS : d.V ≤ d.S := d.action.le_planeStabilizer d.T d.sylow_le hVM 1
  have hVp : IsPGroup 2 d.V := by
    let _ := d.action.elementary
    exact IsElementaryAbelian.isPGroup 2 d.V
  have hVne : d.V ≠ ⊥ := by
    intro he
    have hc : Nat.card d.V = 16 := d.action.card_vector
    have hc1 : Nat.card d.V = 1 := d.V.card_eq_one.mpr he
    omega
  have hNV : normalizer (d.V : Set G) ≤ d.M :=
    hM.2 ⟨d.V, hVne, hVp, rfl⟩ d.action.normalizes
  have hYM : d.Yplus ≤ d.M := by
    rcases d.choice with h | ⟨_, h⟩
    · exact h ▸ Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
    · rw [h]
      exact (map_subtype_le _).trans
        (inf_le_left.trans (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))
  have hw := componentImage_twoCore_witness hLI hIeq P hP hZ hLM hVS hVM hVp
    d.action.normalizes ((Subgroup.centralizer_le_normalizer _).trans hNV)
    hYM (inf_le_left.trans d.sylow_le) (le_sup_left.trans hI.1.2) hF h25
  exact ⟨(componentImage I L d.M).pCoreIn 2, hw.1,
    isPGroup_pCoreIn 2 _, hw.2.symm⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo

end
