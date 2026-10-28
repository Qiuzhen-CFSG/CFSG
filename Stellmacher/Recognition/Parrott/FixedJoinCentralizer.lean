module
public import Stellmacher.Recognition.Parrott.CoreInvolutionGeometry
public import Stellmacher.Recognition.Parrott.OuterInvolutionFixedSpace
public import Theory.GroupAction.FixedCoatomDisplacement
public import Theory.GroupTheory.RelativeCentralLayerCentralizerIndex

/-!
# Self-centralization of the core involution fixed join

Put H=C_G(z), J=O₂(H), and E=J′, embedded in G. For an involution
a in J outside E, the elementary subgroup F=⟨a⟩(E∩C_G(a)) is its own
centralizer. Its intersection Z with E is a hyperplane of E.

An element centralizing F lies in H and fixes Z pointwise, so its action
on E squares to one. Since C_G(E)=E, its square lies in E. An element
outside J with this property fixes at most eight elements of E, whereas
Z has sixteen elements. Thus C_G(F) lies in J. Finally [J,E] lies in
⟨z⟩, and the relative centralizer index over the fixed hyperplane is at
most two. This bounds |C_G(F)| by 32=|F|.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.675, opening of §2.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Stellmacher.Recognition

/-- The actual elementary fixed join of a core involution is self-centralizing. -/
public theorem parrott_core_involution_fixed_join_centralizer
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ a : G, a ∈ J.map H.subtype → orderOf a = 2 → a ∉ E →
      let F := zpowers a ⊔ (E ⊓ centralizer ({a} : Set G))
      centralizer (F : Set G) = F := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let embed := H.subtype.comp J.subtype
  let E := D.map embed
  let K := J.map H.subtype
  change ∀ a : G, a ∈ K → orderOf a = 2 → a ∉ E → _
  intro a ha ha2 haE
  let Z := E ⊓ centralizer ({a} : Set G)
  let F := zpowers a ⊔ Z
  let C := centralizer (F : Set G)
  change C = F
  obtain ⟨hFelem, hFcard, _, hZcard, _, hzZ, _, hEC, _, _⟩ :=
    parrott_core_involution_fixed_join z h a ha ha2 haE
  let : IsElementaryAbelian 2 F := hFelem
  obtain ⟨hcenter, _, _, _, hUpper, hElem, hDcard, _⟩ :=
    parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map embed
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := D) (f := embed)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hEJ : E ≤ K := by
    rw [show E = DH.map H.subtype from (map_map _ _ _).symm]
    exact map_mono (map_subtype_le D)
  have hCE : centralizer (E : Set G) = E := parrott_derived_centralizer z h
  have hZF : Z ≤ F := le_sup_right
  have hCH : C ≤ H := by
    intro c hc
    exact mem_centralizer_singleton_iff.mpr (hc z (hZF hzZ)).symm
  have hHN : H ≤ normalizer (E : Set G) := by
    let : DH.Characteristic := inferInstance
    have hh := le_normalizer_map (H := DH) H.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, DH, map_map] using hh
  have hZindex : (Z.subgroupOf E).index = 2 := by
    have hcard : Nat.card (Z.subgroupOf E) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ E from inf_le_left)).toEquiv).trans hZcard
    have hh := (Z.subgroupOf E).index_mul_card
    rw [hcard, hEcard] at hh
    omega
  have hCK : C ≤ K := by
    intro c hc
    let cH : H := ⟨c, hCH hc⟩
    let cN : normalizer (E : Set G) := ⟨c, hHN (hCH hc)⟩
    let b : MulAut E := E.normalizerMonoidHom cN
    have hZfixed : Z.subgroupOf E ≤ FixedPoints.subgroup (zpowers b) E := by
      intro e he mover
      have hb : b e = e := by
        apply Subtype.ext
        change c * (e : G) * c⁻¹ = (e : G)
        exact mul_inv_eq_iff_eq_mul.mpr (hc (e : G) (hZF he)).symm
      exact smul_eq_self_of_mem_zpowers mover.property hb
    have hb2 : b ^ 2 = 1 := MulAut.square_eq_one_of_fixed_index_dvd_two b
      ((index_dvd_of_le hZfixed).trans (by rw [hZindex]))
    have hc2E : c ^ 2 ∈ E := by
      have hh : cN ^ 2 ∈ E.normalizerMonoidHom.ker := by
        change E.normalizerMonoidHom (cN ^ 2) = 1
        rw [map_pow]
        exact hb2
      rw [normalizerMonoidHom_ker] at hh
      exact hCE ▸ hh
    have hc2J : cH ^ 2 ∈ J := by
      obtain ⟨x, hx, hxc⟩ := hEJ hc2E
      have heq : x = cH ^ 2 := Subtype.ext hxc
      exact heq ▸ hx
    by_contra hcK
    have hcJ : cH ∉ J := fun hh => hcK (mem_map_of_mem H.subtype hh)
    have hbound := parrott_outer_square_mem_core_fixed_card_le z h cH hc2J hcJ
    have hZC : Z.subgroupOf E ≤ (centralizer ({c} : Set G)).subgroupOf E := by
      intro e he
      exact mem_centralizer_singleton_iff.mpr (hc (e : G) (hZF he))
    have hcard : Nat.card (Z.subgroupOf E) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ E from inf_le_left)).toEquiv).trans hZcard
    have hh := card_le_of_le hZC
    rw [hcard] at hh
    change Nat.card ((centralizer ({c} : Set G)).subgroupOf E) ≤ 8 at hbound
    omega
  have hcommKE : ⁅K, E⁆ ≤ zpowers z := by
    have hh : ⁅(⊤ : Subgroup J), D⁆ ≤ center J := by
      rw [commutator_comm, show D = Subgroup.upperCentralSeries J 2 from hUpper]
      simpa only [Subgroup.upperCentralSeries_one] using commutator_upperCentralSeries_top_le J 1
    have hm := map_mono (f := embed) hh
    rw [map_commutator, ← MonoidHom.range_eq_map] at hm
    rw [show embed = H.subtype.comp J.subtype from rfl,
      MonoidHom.range_comp, range_subtype] at hm
    exact hm.trans_eq hcenter
  have hCZ : C ≤ centralizer (Z : Set G) := by
    intro c hc e he
    exact hc e (hZF he)
  have hCz : C ≤ centralizer (zpowers z : Set G) := by
    intro c hc
    exact (centralizer_le (zpowers_le.mpr (hZF hzZ))) hc
  have hindex : (centralizer (E : Set G)).relIndex C ≤ 2 := by
    have hh := relIndex_centralizer_le_card_of_central_index_two_layer
      C E Z (zpowers z) hCZ hCz hZindex
      ((commutator_mono hCK le_rfl).trans hcommKE)
    simpa only [Nat.card_zpowers, h.involution] using hh
  have hECcard : Nat.card (E.subgroupOf C) = 16 := by
    have hh := card_map_of_injective (K := E.subgroupOf C) (f := C.subtype)
      C.subtype_injective
    rw [subgroupOf_map_subtype, show E ⊓ C = Z from hEC] at hh
    exact hh.symm.trans hZcard
  have hCcard : Nat.card C ≤ 32 := by
    have hh := (E.subgroupOf C).card_mul_index
    rw [hECcard] at hh
    rw [hCE] at hindex
    change (E.subgroupOf C).index ≤ 2 at hindex
    omega
  have hFC : F ≤ C := le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact (eq_of_le_of_card_ge hFC (hCcard.trans_eq hFcard.symm)).symm

end Stellmacher.Recognition
