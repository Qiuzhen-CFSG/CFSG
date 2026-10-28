module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.QuotientMaximality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroup
public import Theory.GroupTheory.PCoreCentralizerQuotient
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup

/-!
# Locality of the rank-one component quotient

For the actual quotient `I⁺ = I/C_I(L)`, characteristic two passes from
`M ∩ I` to its image by central-kernel descent in `M ∩ L`, followed by
extension by a two-group. This uses the rank-independent descent theorem
also used in the rank-two argument.

The two-local witness is `O₂(M_I⁺)`. An earlier plane lies in `O₂(M_I)`
and has centralizer contained in `M`, making `O₂(M_I)` self-centralizing
inside `I`. Theorem 15.3.25 applies to its actual normalizer and forces
that normalizer to be `M_I`. The two-group action kernel lies in this
core, so its full normalizer equality passes to the quotient. The image
core is nontrivial because otherwise the plane centralizes the outside
component. This adapts the core-normalizer argument of
`RankTwo.QuotientLocal.TwoLocal` to relative plane invariance; no rank-two
shadow or quotient-output hypothesis is used.

Finally the four-group embeds faithfully by the bare fixed-point lemma,
and the earlier quotient transport results assemble `QuotientConditions`.
Component placement and the full `ReducedConfiguration` construction
remain with the rank-one reduction owner. Every hypothesis used here is
an explicit earlier local conclusion; no quotient locality is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11(3),(7), 15.3.25, and the proof of 15.3.41 and 15.3.43(e),
printed pp.1123, 1130, and 1138--1140.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentAction
variable {G : Type*} [Group G] [Finite G]

private theorem intersection_core_selfCentralizing
    {I M V : Subgroup G} (hVI : V ≤ I) (hVM : V ≤ M)
    (hVp : IsPGroup 2 V) (hMV : M ⊓ I ≤ normalizer (V : Set G))
    (hCV : centralizer (V : Set G) ≤ M)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G)) :
    centralizer ((M.subgroupOf I).pCoreIn 2 : Set I) ≤ (M.subgroupOf I).pCoreIn 2 := by
  let H := M.subgroupOf I
  have hV : V.subgroupOf I ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hVp.comap_subtype (comap_mono hVM) (by
      rw [← subgroupOf_normalizer_eq hVI]
      exact fun x hx => hMV ⟨hx, x.property⟩)
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
    (hMV : M ⊓ I ≤ normalizer (V : Set G)) (hCV : centralizer (V : Set G) ≤ M)
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
        exact fun x hx => hMV ⟨hx, x.property⟩)
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
normalizer is M_I⁺. The hypotheses only require relative plane invariance in `M ∩ I`
and the earlier plane-centralizer control; no quotient locality is assumed. -/
theorem image_twoCore_witness
    {I L M V Y S : Subgroup G} (d : ComponentAction I L) (hIeq : I = L ⊔ S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hz : (center L).map L.subtype = L.pCoreIn 2) (hLM : ¬ L ≤ M)
    (hVS : V ≤ S) (hVM : V ≤ M) (hVp : IsPGroup 2 V)
    (hMV : M ⊓ I ≤ normalizer (V : Set G)) (hCV : centralizer (V : Set G) ≤ M)
    (hYM : Y ≤ M) (hSM : S ≤ M) (hYI : Y ≤ I)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G))
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A) :
    (d.image M).pCoreIn 2 ≠ ⊥ ∧
      normalizer ((d.image M).pCoreIn 2 : Set d.Quotient) =
        d.image M := by
  let q := d.quotientMap
  let H := M.subgroupOf I
  let D := H.pCoreIn 2
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hSp : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hk : IsPGroup 2 q.ker := (show q.ker = d.kernel from QuotientGroup.ker_mk' _).symm ▸
    d.kernel_isTwoGroup hSp hIeq hz
  have hSI : S ≤ I := hIeq ▸ le_sup_right
  have hVI : V ≤ I := hVS.trans hSI
  have hVD : V.subgroupOf I ≤ D :=
    le_pCoreIn_of_normalizes hVp.comap_subtype (comap_mono hVM) (by
      rw [← subgroupOf_normalizer_eq hVI]
      exact fun x hx => hMV ⟨hx, x.property⟩)
  have hVk : ¬ V.subgroupOf I ≤ q.ker := by
    intro h
    have hv : V ≤ centralizer (L : Set G) := by
      intro v hv l hl
      have hh := h (show (⟨v, hVI hv⟩ : I) ∈ V.subgroupOf I from hv)
      rw [show q.ker = (centralizer (L : Set G)).subgroupOf I from QuotientGroup.ker_mk' d.kernel] at hh
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
  have himage : D.map q = (d.image M).pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup q hk H
  refine ⟨?_, ?_⟩
  · rw [← himage]
    intro he
    exact hVk (hVD.trans ((D.map_eq_bot_iff).mp he))
  · apply Subgroup.comap_injective hq
    rw [comap_normalizer_eq_of_surjective _ hq, ← himage,
      comap_map_eq_self hkerD, hN]
    exact (comap_map_eq_self hkerH).symm

/-- Characteristic two descends to the actual local image. The restriction
of the kernel to `M ∩ L` is central, and the quotient above that subgroup
is a two-group. An arbitrary two-kernel would not suffice. -/
theorem image_characteristicTwo {I L M S : Subgroup G}
    (d : ComponentAction I L) (hS : IsPGroup 2 S) (hgen : I = L ⊔ S)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G)) :
    generalizedFitting (d.image M) = pCore 2 (d.image M) := by
  have hc : centralizer (pCore 2 (M ⊓ I : Subgroup G) : Set (M ⊓ I : Subgroup G)) ≤
      pCore 2 (M ⊓ I : Subgroup G) := by
    rw [← hF]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hH := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (show M ⊓ I ≤ I from inf_le_right))).mpr hc
  rw [inf_subgroupOf_right] at hH
  let := normal_subgroupOf_of_le_normalizer d.normalizes
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply d.quotientMap.centralizer_pCore_image_of_ker_le_centralizer
    (L.subgroupOf I) (d.quotient_component_isTwoGroup hS hgen) _ (M.subgroupOf I) hH
  rw [show d.quotientMap.ker = d.kernel from QuotientGroup.ker_mk' _]
  exact d.kernel_eq_centralizer.le

/-- Actual maximality, including characteristic two of the subgroup itself,
using 15.3.25 for every competing outside overgroup. -/
theorem image_maximal {I L M Y S : Subgroup G} (d : ComponentAction I L)
    (hIeq : I = L ⊔ S) (hz : (center L).map L.subtype = L.pCoreIn 2)
    (hI : I ∈ outsideFamily Y S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYM : Y ≤ M) (hSM : S ≤ M)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G))
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A) :
    Maximal (fun X : Subgroup d.Quotient => generalizedFitting X = pCore 2 X) (d.image M) := by
  refine ⟨d.image_characteristicTwo (hP ▸ P.isPGroup'.map I.subtype) hIeq hF, ?_⟩
  intro J hJ hMJ
  exact (d.image_maximal_overgroups hIeq hz hI P hP hYM hSM h25 J hMJ hJ).le

/-- The two-local assertion uses the nontrivial image core and its full
normalizer, with the plane normalizer bound from 15.3.11(3). -/
theorem image_isTwoLocal {I L M V Y S : Subgroup G}
    (d : ComponentAction I L) (hIeq : I = L ⊔ S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hz : (center L).map L.subtype = L.pCoreIn 2) (hLM : ¬ L ≤ M)
    (hVS : V ≤ S) (hVp : IsPGroup 2 V)
    (hMV : M ⊓ I ≤ normalizer (V : Set G)) (hNV : normalizer (V : Set G) ≤ M)
    (hYM : Y ≤ M) (hSM : S ≤ M) (hYI : Y ≤ I)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G))
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A) :
    IsTwoLocal (d.image M) := by
  have hw := d.image_twoCore_witness hIeq P hP hz hLM hVS (hVS.trans hSM) hVp
    hMV ((Subgroup.centralizer_le_normalizer _).trans hNV) hYM hSM hYI hF h25
  exact ⟨(d.image M).pCoreIn 2, hw.1, isPGroup_pCoreIn 2 _, hw.2.symm⟩

/-- The source four-group has a faithful image directly from its action
and theta identity. No reduction-output record is assumed. -/
theorem image_fourGroup_from_plane {I L M V Y S : Subgroup G}
    (d : ComponentAction I L) (hSI : S ≤ I) (hSM : S ≤ M)
    (hVS : V ≤ S) (helem : IsElementaryAbelian 2 V) (hcard : Nat.card V = 4)
    (hYL : Y ≤ L) (hθ : theta (M ⊓ I) = Y)
    (hMV : M ⊓ I ≤ normalizer (V : Set G)) (hcomm : ⁅V, Y⁆ = V) :
    Nonempty (V ≃* d.image V) ∧ d.image V ≤ d.image M ∧
      ((d.image V).subgroupOf (d.image M)).Normal ∧
      ⁅d.image V, d.image Y⁆ = d.image V := by
  let : IsElementaryAbelian 2 V := helem
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : IsKleinFour V := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hVI : V ≤ I := hVS.trans hSI
  have hgen : theta Y = Y := by rw [← hθ, theta_idempotent]
  have hYM : Y ≤ M ⊓ I := hθ ▸ theta_le (M ⊓ I)
  obtain ⟨hle, hn⟩ := image_normal_in_local d hVI (hVS.trans hSM) hMV
  exact ⟨⟨fourGroupImageEquiv d hVI hYL hgen (hYM.trans hMV) hcomm⟩,
    hle, hn, image_commutator_eq d hVI (hYL.trans d.component_le) hcomm⟩

/-- All model-independent clauses of 15.3.43(e), after the upstream
component placement, from the genuine local equalities and plane control.
This constructs the quotient-output record; full rank-one reduction and
the source model alternatives remain with the parent assembly. -/
theorem quotientConditions_of_plane {I L M V Y S : Subgroup G}
    (d : ComponentAction I L) (hI : I ∈ minimalOutsideFamily Y S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hSM : S ≤ M) (hcomp : IsComponent I (L.subgroupOf I))
    (hz : (center L).map L.subtype = L.pCoreIn 2) (hLM : ¬ L ≤ M)
    (hYL : Y ≤ L) (hθ : theta (M ⊓ I) = Y)
    (hres : Y = threeResidualIn (M ⊓ I)) (hshadow : SymmetricThreeShadow Y S)
    (hF : generalizedFitting (M ⊓ I : Subgroup G) = pCore 2 (M ⊓ I : Subgroup G))
    (hVS : V ≤ S) (helem : IsElementaryAbelian 2 V) (hcard : Nat.card V = 4)
    (hMV : M ⊓ I ≤ normalizer (V : Set G)) (hNV : normalizer (V : Set G) ≤ M)
    (hcomm : ⁅V, Y⁆ = V)
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A) :
    QuotientConditions d Y S M ∧ Nonempty (V ≃* d.image V) := by
  have hgen := eq_component_join_sylow hI P hP d.component_le hYL hLM
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hSI : S ≤ I := hP ▸ map_subtype_le _
  have hYI := hYL.trans d.component_le
  have hYM : Y ≤ M := (hθ ▸ theta_le (M ⊓ I)).trans inf_le_left
  have hk := d.kernel_isTwoGroup hS hgen hz
  let : IsElementaryAbelian 2 V := helem
  refine ⟨{
    fitting := d.image_generalizedFitting hcomp hS hgen
    simple := d.image_simple_of_component hcomp
    twoLocal := d.image_isTwoLocal hgen P hP hz hLM hVS
      (IsElementaryAbelian.isPGroup 2 V) hMV hNV hYM hSM hYI hF h25
    residual := d.image_threeResidual hres
    radical := ?_
    shadow := d.image_shadow hYI hSI hk hshadow
    maximal := d.image_maximal hgen hz hI.1 P hP hYM hSM hF h25 },
    (d.image_fourGroup_from_plane hSI hSM hVS helem hcard hYL hθ hMV hcomm).1⟩
  rw [d.image_radical (sup_le hYI hSI) hk, d.image_sup hYI hSI]

end CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentAction
