module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.MovedPlane
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonProduct
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The moved-plane product in the literal involution centralizer

Apply the relative Thompson factor theorem inside H=C_G(z), using its
actual omega-center orbit V_H and quotient H/C_H(V_H). Mapping the intrinsic
commutator and centralizer through H's inclusion gives the original ambient
subgroups: |[V_H,I]|=4, [V_H,I]∩C_G(I)=1, and H=I C_H([V_H,I]).

This supplies the product and fixed-vector exclusion used by NormalizerProduct.
Single-factor selection and Thompson noncentrality remain explicit here and
are discharged in that file's two-core-kernel, Baumann-bound application.
Source: Aschbacher–Smith 13.4.8, printed p.905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_thompson_plane_structure
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hmodel :
      let H := centralizer ({z} : Set G)
      let U := (centralizerOmegaOrbit T z).subgroupOf H
      letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
      let q := QuotientGroup.mk' (centralizer (U : Set H))
      Nonempty ((((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q) ≃*
        Equiv.Perm (Fin 3))) :
    let H := centralizer ({z} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    let W := (⁅centralizerOmegaOrbit T z,I⁆ : Subgroup G)
    Nat.card W = 4 ∧ Disjoint W (centralizer (I : Set G)) ∧
      I ⊔ (H ⊓ centralizer (W : Set G)) = H := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let := hU.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  have hq := QuotientGroup.mk'_surjective (centralizer (U : Set H))
  have hker : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' _
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
  have hUR : U ≤ R.subgroupOf H :=
    fun _ hx => hQR (centralizerOmegaOrbit_le_core h₀ hz hz1 hx)
  have hmapJ : (elementaryAbelianMaxJ (R.subgroupOf H)).map H.subtype =
      elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hRH]
  have hJi : ¬ elementaryAbelianMaxJ (R.subgroupOf H) ≤ q.ker := by
    rw [hker]
    intro hc
    apply hJ
    rw [← hmapJ]
    rintro x ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val (hc ha ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hspan : conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤ =
      (conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_conjugateSpanBy, hmapJ, ← MonoidHom.range_eq_map, H.range_subtype,
      map_subgroupOf_eq_of_le]
    exact conjugateSpanBy_le_self ((sSup_le fun _ hA => hA.1).trans hRH)
  have hm : Nonempty (((conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤).map q) ≃*
      Equiv.Perm (Fin 3)) := by
    rw [hspan]
    exact hmodel
  let N := conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤
  have hmap : (⁅U,N⁆ : Subgroup H).map H.subtype =
      ⁅centralizerOmegaOrbit T z,conjugateSpanBy (elementaryAbelianMaxJ R) H⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz)]
    dsimp only [N]
    rw [map_conjugateSpanBy, hmapJ, ← MonoidHom.range_eq_map, H.range_subtype]
  have hd := ChapterB.relative_thompson_span_moved_disjoint U (R.subgroupOf H) hUR
    q hq hker hJi hsolv hU.quotient_pCore_eq_bot hm
  have hp := ChapterB.relative_thompson_span_centralizer_product U (R.subgroupOf H) hUR
    q hq hker hJi hsolv hU.quotient_pCore_eq_bot hm
  have hNmap : N.map H.subtype = conjugateSpanBy (elementaryAbelianMaxJ R) H := by
    dsimp only [N]
    rw [map_conjugateSpanBy,hmapJ,← MonoidHom.range_eq_map,H.range_subtype]
  refine ⟨centralizer_thompson_commutator_card_of_single_factor h₀ hz hz1 R hRT hQR hJ hsolv hmodel,?_,?_⟩
  · apply disjoint_def.mpr
    intro w hw hc
    rw [← hmap] at hw
    obtain ⟨v,hv,rfl⟩ := hw
    have hcv : v ∈ centralizer (N : Set H) := by
      intro a ha
      exact Subtype.ext (hc a.val (hNmap ▸ mem_map_of_mem H.subtype ha))
    exact congrArg Subtype.val ((disjoint_def.mp hd) hv hcv)
  · have hh := congrArg (fun A : Subgroup H => A.map H.subtype) hp
    rw [Subgroup.map_sup,hNmap,← MonoidHom.range_eq_map,H.range_subtype] at hh
    have hc := map_inf_centralizer_of_injective H.subtype H.subtype_injective
      (⊤ : Subgroup H) (⁅U,N⁆ : Subgroup H)
    rw [← MonoidHom.range_eq_map,H.range_subtype,hmap,top_inf_eq] at hc
    rwa [← hc] at hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
