module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Inheritance
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Ranks
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# Thompson action images and offender selection after replacement

A Sylow overgroup has the same maximum elementary order as the whole group.
If it also has the same action image, conjugacy into the common Sylow subgroup
shows that its elementary Thompson subgroup has the same action image.
A refined Frattini argument supplies the centralizer-image hypothesis for `H`.
Together with the original `I = I₀ C_I(V_E/E)` supplement, this identifies the
images of `J(C_H(E))` and the original `I₀` in every action killing the section
kernel. It does not identify these subgroups by intersection.

The comparison also transfers escape from `M` to the temporary Thompson group.
The unchanged Sylow subgroup and maximum-family comparison then supply an actual
maximum elementary subgroup with nontrivial temporary core-quotient image.
The core-kernel containment in the last two lemmas is discharged in `Replacement`
using `temporaryCore_eq_quotientCentralizer` from `Replacement/Core.lean`.

The refined Frattini image proof adapts the already checked subgroup-correction
argument in `Descent/Frattini.lean` to an arbitrary normal subgroup.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G K : Type*} [Group G] [Group K] [Finite G]

/-- A Sylow overgroup has the same maximum elementary order as the ambient group. -/
theorem maxFamily_of_sylow_overgroup (P : Sylow 2 G) (D A : Subgroup G)
    (hPD : (P : Subgroup G) ≤ D) (hA : A ∈ elementaryAbelianMaxSubgroups D) :
    A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G) := by
  refine ⟨le_top, hA.2.1, fun B _ hB => ?_⟩
  obtain ⟨S, hBS⟩ := hB.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  let e := MulAut.conj g
  have hSP : (S : Subgroup G).map e.toMonoidHom = (P : Subgroup G) := by
    change ((g • S : Sylow 2 G) : Subgroup G) = (P : Subgroup G)
    rw [hg]
  have hBD : B.map e.toMonoidHom ≤ D := ((map_mono hBS).trans hSP.le).trans hPD
  have hc := hA.2.2 (B.map e.toMonoidHom) hBD (hB.map e.toMonoidHom)
  rwa [card_map_of_injective e.injective] at hc

/-- Thompson monotonicity here follows from the common Sylow subgroup. -/
theorem maxJ_of_sylow_overgroup_le (P : Sylow 2 G) (D : Subgroup G)
    (hPD : (P : Subgroup G) ≤ D) :
    elementaryAbelianMaxJ D ≤ elementaryAbelianMaxJ (⊤ : Subgroup G) := by
  exact sSup_le fun A hA => le_sSup (maxFamily_of_sylow_overgroup P D A hPD hA)

omit [Finite G] in
/-- The maximum-elementary construction is normalized by its own overgroup. -/
theorem le_normalizer_maxJ (D : Subgroup G) :
    D ≤ normalizer (elementaryAbelianMaxJ D : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj g) D).symm.trans
    (congrArg elementaryAbelianMaxJ (mem_normalizer_iff_map_conj_eq.mp (D.le_normalizer hg)))

/-- A Sylow overgroup with the same action image has the same Thompson action image.
No assertion about intersection of Thompson subgroups is used. -/
theorem maxJ_image_of_sylow_overgroup (P : Sylow 2 G) (D : Subgroup G)
    (hPD : (P : Subgroup G) ≤ D) (f : G →* K)
    (himage : ∀ g : G, ∃ d ∈ D, f d = f g) :
    (elementaryAbelianMaxJ D).map f = (elementaryAbelianMaxJ (⊤ : Subgroup G)).map f := by
  apply le_antisymm (map_mono (maxJ_of_sylow_overgroup_le P D hPD))
  rw [map_le_iff_le_comap]
  apply sSup_le
  intro A hA a ha
  obtain ⟨S, hAS⟩ := hA.2.1.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  let e := MulAut.conj g
  have hSP : (S : Subgroup G).map e.toMonoidHom = (P : Subgroup G) := by
    change ((g • S : Sylow 2 G) : Subgroup G) = (P : Subgroup G)
    rw [hg]
  have hAD : A.map e.toMonoidHom ≤ D := ((map_mono hAS).trans hSP.le).trans hPD
  have hmax : A.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups D := by
    refine ⟨hAD, hA.2.1.map e.toMonoidHom, fun B _ hB => ?_⟩
    rw [card_map_of_injective e.injective]
    exact hA.2.2 B le_top hB
  obtain ⟨d, hd, hdf⟩ := himage g
  have hconj : e a ∈ elementaryAbelianMaxJ D := le_sSup hmax (mem_map_of_mem e.toMonoidHom ha)
  have hback : d⁻¹ * e a * d ∈ elementaryAbelianMaxJ D := by
    simpa only [inv_inv, SetLike.mem_coe] using
      (le_normalizer_maxJ D (D.inv_mem hd) (e a)).mp hconj
  have hmap := mem_map_of_mem f hback
  have he : f (d⁻¹ * e a * d) = f a := by
    simp only [map_mul, map_inv, e, MulAut.conj_apply, hdf]
    group
  change f a ∈ (elementaryAbelianMaxJ D).map f
  rw [← he]
  exact hmap

/-- The Frattini supplement preserves the image of the original Thompson subgroup
in every action killing the actual section kernel. -/
theorem lineI0_image_eq
    (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (f : lineNormalizer E →* K)
    (hker : (Descent.sectionKernel V E).subgroupOf (lineNormalizer E) ≤ f.ker) :
    ((lineI0 T V E).subgroupOf (lineNormalizer E)).map f =
      ((lineI E).subgroupOf (lineNormalizer E)).map f := by
  apply le_antisymm (map_mono (comap_mono inf_le_left))
  rintro _ ⟨i, hi, rfl⟩
  have hip : (i : G) ∈ (lineI0 T V E : Set G) * (Descent.thompsonKernel V E : Set G) := by
    rw [← Descent.frattini_correction T V E hEV P hP]
    exact hi
  obtain ⟨j, hj, k, hk, hjk⟩ := hip
  let jL : lineNormalizer E := ⟨j, lineI_le_lineNormalizer E hj.1⟩
  let kL : lineNormalizer E := ⟨k, Descent.sectionKernel_le V E hk.2⟩
  have he : jL * kL = i := Subtype.ext hjk
  have hkf : f kL = 1 := hker hk.2
  exact mem_map.mpr ⟨jL, hj, by rw [← he, map_mul, hkf, mul_one]⟩

/-- Escape of the original `I` from `M` persists in its fixed original `I₀`. -/
theorem lineI0_not_le_lineM (M T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E) :
    ¬ lineI0 T V E ≤ lineM M E := by
  intro hI0
  apply hI
  intro i hi
  have hip : i ∈ (lineI0 T V E : Set G) * (Descent.thompsonKernel V E : Set G) := by
    rw [← Descent.frattini_correction T V E hEV P hP]
    exact hi
  obtain ⟨j, hj, k, hk, rfl⟩ := hip
  exact (lineM M E).mul_mem (hI0 hj) (Descent.thompsonKernel_le_lineM M V E hEV hNM hk)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_normal_intersection (L C : Subgroup G) (hCL : C ≤ L)
    [(C.subgroupOf L).Normal] (P : Sylow 2 L) :
    ∃ S : Sylow 2 C, (S : Subgroup C).map C.subtype =
      (P : Subgroup L).map L.subtype ⊓ C := by
  let D := C.subgroupOf L
  obtain ⟨S, hS⟩ := P.exists_sylow_map_eq_inf_of_normal D
  let e : D ≃* C := subgroupOfEquivOfLe hCL
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup D).map e.toMonoidHom).map C.subtype = _
  have he : C.subtype.comp e.toMonoidHom = L.subtype.comp D.subtype := rfl
  rw [map_map, he, ← map_map, hS, map_inf _ _ _ L.subtype_injective,
    map_subgroupOf_eq_of_le hCL]

/-- The original line Sylow subgroup meets `C_G(E)` in its actual Sylow subgroup. -/
theorem centralizer_sylow (T E : Subgroup G) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    ∃ S : Sylow 2 (centralizer (E : Set G)),
      (S : Subgroup (centralizer (E : Set G))).map (centralizer (E : Set G)).subtype =
        lineT T E ⊓ centralizer (E : Set G) := by
  obtain ⟨S, hS⟩ := sylow_normal_intersection (lineNormalizer E)
    (centralizer (E : Set G)) (Subgroup.centralizer_le_normalizer _) P
  exact ⟨S, by rwa [hP] at hS⟩

/-- The temporary centralizer has the same Sylow subgroup as the original centralizer. -/
theorem temporaryCentralizer_sylow (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    ∃ S : Sylow 2 (temporaryCentralizer T V E),
      (S : Subgroup (temporaryCentralizer T V E)).map (temporaryCentralizer T V E).subtype =
        lineT T E ⊓ centralizer (E : Set G) := by
  let H := temporaryLineNormalizer T V E
  let C := temporaryCentralizer T V E
  have hNC : lineNormalizer E ≤ normalizer (centralizer (E : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (E : Set G))).mp inferInstance
  have hn : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer (inf_le_left.trans hNC)).trans inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hn
  obtain ⟨PH, hPH⟩ := lineT_sylow_temporary T V E hEV P hP
  obtain ⟨S, hS⟩ := sylow_normal_intersection H C inf_le_left PH
  refine ⟨S, ?_⟩
  rw [hPH] at hS
  rw [hS]
  change lineT T E ⊓ (H ⊓ centralizer (E : Set G)) = _
  rw [← inf_assoc, inf_eq_left.mpr (lineT_le_temporary T V E hEV)]

/-- Every generator of the temporary Thompson subgroup is a genuine generator of
original `I`; containment in `H` then places it in the original `I₀`. -/
theorem temporaryMaxJ_le_lineI0 (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    elementaryAbelianMaxJ (temporaryCentralizer T V E) ≤ lineI0 T V E := by
  let C := centralizer (E : Set G)
  let D := (temporaryCentralizer T V E).subgroupOf C
  obtain ⟨S, hS⟩ := centralizer_sylow T E P hP
  have hSD : (S : Subgroup C) ≤ D := by
    intro c hc
    have hh : (c : G) ∈ lineT T E ⊓ centralizer (E : Set G) :=
      hS ▸ mem_map_of_mem C.subtype hc
    exact ⟨lineT_le_temporary T V E hEV hh.1, hh.2⟩
  have hJ := map_mono (f := C.subtype) (maxJ_of_sylow_overgroup_le S D hSD)
  rw [← elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective,
    ← elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective,
    map_subgroupOf_eq_of_le (show temporaryCentralizer T V E ≤ C from inf_le_right),
    ← MonoidHom.range_eq_map, C.range_subtype] at hJ
  rw [lineI0_eq_inf_temporary]
  refine le_inf hJ ?_
  exact (sSup_le fun _ hA => hA.1).trans inf_le_left

/-- The Sylow maximum family already contained in `C_G(E)` remains contained in
`C_H(E)`, supplying the comparison witness required by offender selection. -/
theorem exists_max_in_temporaryCentralizer (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G)) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (lineT T E), B ≤ temporaryCentralizer T V E := by
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty (lineT T E)
  exact ⟨B, hB, le_inf (hB.1.trans (lineT_le_temporary T V E hEV)) ((le_sSup hB).trans hJ)⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G K : Type*} [Group G] [Group K] [Finite G]

private theorem normal_frattini_image (I N : Subgroup G) [I.Normal] [N.Normal]
    (P : Sylow 2 N) (f : G →* K) (hker : N ≤ f.ker) :
    (I ⊓ normalizer ((P : Subgroup N).map N.subtype : Set G)).map f = I.map f := by
  let R := (P : Subgroup N).map N.subtype
  let W := I ⊔ R
  let D := N ⊓ W
  have hRN : R ≤ N := map_subtype_le _
  have hRD : R ≤ D := le_inf hRN le_sup_right
  have hidxN : ¬ 2 ∣ R.relIndex N := by
    change ¬ 2 ∣ ((P : Subgroup N).map N.subtype |>.comap N.subtype).index
    rw [comap_map_eq_self_of_injective N.subtype_injective]
    exact P.not_dvd_index
  have hidxD : ¬ 2 ∣ R.relIndex D := by
    intro hd
    exact hidxN (dvd_trans hd (dvd_of_mul_right_eq _ (relIndex_mul_relIndex R D N hRD inf_le_left)))
  let PD : Sylow 2 D := ((P.isPGroup'.map N.subtype).comap_subtype (K := D)).toSylow hidxD
  have hPD : (PD : Subgroup D).map D.subtype = R := map_subgroupOf_eq_of_le hRD
  have hWD : W ≤ normalizer (D : Set G) :=
    (le_inf le_normalizer_of_normal W.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hfr : W ≤ normalizer (R : Set G) ⊔ D := by
    simpa only [hPD] using le_normalizer_sylow_sup D W inf_le_right hWD PD
  have hNRD : normalizer (R : Set G) ≤ normalizer (D : Set G) := by
    have hnW : normalizer (R : Set G) ≤ normalizer (W : Set G) :=
      (le_inf le_normalizer_of_normal le_rfl).trans (normalizer_inf_normalizer_le_normalizer_sup I R)
    exact (le_inf le_normalizer_of_normal hnW).trans inf_normalizer_le_normalizer_inf
  apply le_antisymm (map_mono inf_le_left)
  rintro _ ⟨i, hi, rfl⟩
  have hip : i ∈ (D : Set G) * (normalizer (R : Set G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hNRD, sup_comm]
    exact hfr (mem_sup_left hi)
  obtain ⟨n, hn, d, hd, hnd⟩ := hip
  obtain ⟨j, hj, r, hr, hjr⟩ := mem_sup_of_normal_left.mp hn.2
  have hjN : j ∈ N := by
    have hh := N.mul_mem hn.1 (N.inv_mem (hRN hr))
    rwa [← hjr, mul_inv_cancel_right] at hh
  have he : j * (r * d) = i := by rw [← mul_assoc, hjr]; exact hnd
  have hrdI : r * d ∈ I := by
    have hh := I.mul_mem (I.inv_mem hj) hi
    rw [← he, inv_mul_cancel_left] at hh
    exact hh
  have hjf : f j = 1 := hker hjN
  exact mem_map.mpr ⟨r * d, ⟨hrdI, mul_mem (R.le_normalizer hr) hd⟩,
    by rw [← he]; simp only [map_mul, hjf, one_mul]⟩

/-- Replacing the group preserves the full centralizer action image on the section.
This refined Frattini statement does not need the whole section kernel to centralize `E`. -/
theorem temporaryCentralizer_image_eq (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (f : lineNormalizer E →* K)
    (hker : (Descent.sectionKernel V E).subgroupOf (lineNormalizer E) ≤ f.ker) :
    ((temporaryCentralizer T V E).subgroupOf (lineNormalizer E)).map f =
      ((centralizer (E : Set G)).subgroupOf (lineNormalizer E)).map f := by
  let L := lineNormalizer E
  let N := (Descent.sectionKernel V E).subgroupOf L
  let C := (centralizer (E : Set G)).subgroupOf L
  let : N.Normal := Descent.sectionKernel_normal V E hEV
  let : C.Normal := inferInstance
  obtain ⟨S, hS⟩ := P.exists_sylow_map_eq_inf_of_normal N
  have hmap : ((S : Subgroup N).map N.subtype).map L.subtype = lineQuotientCentralizer T V E := by
    rw [hS, map_inf _ _ _ L.subtype_injective, hP,
      map_subgroupOf_eq_of_le (Descent.sectionKernel_le V E),
      Descent.quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
    rw [lineT, inf_assoc, inf_of_le_right (Descent.sectionKernel_le V E)]
  have hr : (S : Subgroup N).map N.subtype = (lineQuotientCentralizer T V E).subgroupOf L := by
    rw [← hmap, subgroupOf, comap_map_eq_self_of_injective L.subtype_injective]
  have hfr := normal_frattini_image C N S f hker
  have hNrm : normalizer ((S : Subgroup N).map N.subtype : Set L) =
      (normalizer (lineQuotientCentralizer T V E : Set G)).subgroupOf L := by
    rw [hr, ← subgroupOf_normalizer_eq ((lineQuotientCentralizer_le_lineT T V E).trans inf_le_right)]
  rw [hNrm] at hfr
  have he : C ⊓ (normalizer (lineQuotientCentralizer T V E : Set G)).subgroupOf L =
      (temporaryCentralizer T V E).subgroupOf L := by
    ext x
    change ((x : G) ∈ centralizer (E : Set G) ∧ (x : G) ∈ normalizer (lineQuotientCentralizer T V E : Set G)) ↔
      (((x : G) ∈ lineNormalizer E ∧ (x : G) ∈ normalizer (lineQuotientCentralizer T V E : Set G)) ∧
        (x : G) ∈ centralizer (E : Set G))
    exact ⟨fun h => ⟨⟨x.property, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  rwa [he] at hfr

/-- Equal action images and a common Sylow subgroup give equal Thompson action images. -/
theorem maxJ_image_of_common_sylow (C D : Subgroup G) (hDC : D ≤ C)
    (P : Sylow 2 C) (hPD : (P : Subgroup C).map C.subtype ≤ D)
    (f : G →* K) (himage : D.map f = C.map f) :
    (elementaryAbelianMaxJ D).map f = (elementaryAbelianMaxJ C).map f := by
  let B := D.subgroupOf C
  let g := f.comp C.subtype
  have hPB : (P : Subgroup C) ≤ B := fun x hx => hPD (mem_map_of_mem C.subtype hx)
  have hrep : ∀ c : C, ∃ d ∈ B, g d = g c := by
    intro c
    have hc : f c ∈ D.map f := himage.symm ▸ mem_map_of_mem f c.property
    obtain ⟨d, hd, he⟩ := hc
    exact ⟨⟨d, hDC hd⟩, hd, he⟩
  have h := maxJ_image_of_sylow_overgroup P B hPB g hrep
  change (elementaryAbelianMaxJ B).map (f.comp C.subtype) =
    (elementaryAbelianMaxJ (⊤ : Subgroup C)).map (f.comp C.subtype) at h
  rw [← map_map, ← map_map, ← elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective,
    ← elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective,
    map_subgroupOf_eq_of_le hDC, ← MonoidHom.range_eq_map, C.range_subtype] at h
  exact h

omit [Finite G] in
private theorem maxJ_subgroupOf (A L : Subgroup G) (hAL : A ≤ L) :
    elementaryAbelianMaxJ (A.subgroupOf L) = (elementaryAbelianMaxJ A).subgroupOf L := by
  have h := elementaryAbelianMaxJ_map_injective L.subtype L.subtype_injective (A.subgroupOf L)
  rw [map_subgroupOf_eq_of_le hAL] at h
  rw [h]
  exact (comap_map_eq_self_of_injective L.subtype_injective _).symm

/-- The comparison needed by B.5 concerns images: the temporary Thompson subgroup
and the fixed original `I₀` have the same action on `V_E/E`. -/
theorem temporaryMaxJ_image_eq_lineI0 (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (f : lineNormalizer E →* K)
    (hker : (Descent.sectionKernel V E).subgroupOf (lineNormalizer E) ≤ f.ker) :
    ((elementaryAbelianMaxJ (temporaryCentralizer T V E)).subgroupOf (lineNormalizer E)).map f =
      ((lineI0 T V E).subgroupOf (lineNormalizer E)).map f := by
  let L := lineNormalizer E
  let C := (centralizer (E : Set G)).subgroupOf L
  let D := (temporaryCentralizer T V E).subgroupOf L
  let : C.Normal := inferInstance
  obtain ⟨S, hS⟩ := P.exists_sylow_map_eq_inf_of_normal C
  have hSD : (S : Subgroup C).map C.subtype ≤ D := by
    rw [hS]
    intro x hx
    have ht : (x : G) ∈ lineT T E := hP ▸ mem_map_of_mem L.subtype hx.1
    exact ⟨lineT_le_temporary T V E hEV ht, hx.2⟩
  have h := maxJ_image_of_common_sylow C D (comap_mono inf_le_right) S hSD f
    (temporaryCentralizer_image_eq T V E hEV P hP f hker)
  change (elementaryAbelianMaxJ ((temporaryCentralizer T V E).subgroupOf L)).map f =
    (elementaryAbelianMaxJ ((centralizer (E : Set G)).subgroupOf L)).map f at h
  rw [maxJ_subgroupOf (temporaryCentralizer T V E) L (inf_le_left.trans inf_le_left),
    maxJ_subgroupOf (centralizer (E : Set G)) L (Subgroup.centralizer_le_normalizer (E : Set G))] at h
  exact h.trans (lineI0_image_eq T V E hEV P hP f hker).symm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G : Type*} [Group G] [Finite G]

/-- Escape of the original Thompson subgroup forces nontrivial temporary Thompson
image modulo the temporary core. The core-kernel containment is supplied by the
proved core equality. -/
theorem temporaryMaxJ_not_le_core (M T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
    (hcore : temporaryCore T V E ≤ Descent.sectionKernel V E) :
    ¬ elementaryAbelianMaxJ (temporaryCentralizer T V E) ≤ temporaryCore T V E := by
  let L := lineNormalizer E
  let K := (Descent.sectionKernel V E).subgroupOf L
  let : K.Normal := Descent.sectionKernel_normal V E hEV
  let f := QuotientGroup.mk' K
  have hk : K ≤ f.ker := by rw [QuotientGroup.ker_mk']
  intro hJ
  have hmap := temporaryMaxJ_image_eq_lineI0 T V E hEV P hP f hk
  have hzero : ((lineI0 T V E).subgroupOf L).map f = ⊥ := by
    rw [← hmap]
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (comap_mono (hJ.trans hcore)).trans hk
  have hI0K := (Subgroup.map_eq_bot_iff _).mp hzero
  rw [QuotientGroup.ker_mk'] at hI0K
  apply lineI0_not_le_lineM M T V E hEV P hP hNM hI
  intro i hi
  have hiL : i ∈ L := lineI_le_lineNormalizer E hi.1
  have hiK : i ∈ Descent.sectionKernel V E := hI0K (show (⟨i, hiL⟩ : L) ∈
    (lineI0 T V E).subgroupOf L from hi)
  exact ⟨hNM (sectionKernel_le_normalizer V E hEV hiK), hiL⟩

/-- An actual maximum elementary subgroup in the temporary Sylow subgroup has
nonidentity image modulo the temporary core and lies in the temporary centralizer. -/
theorem exists_temporary_max_nontrivial_image (M T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
    (hcore : temporaryCore T V E ≤ Descent.sectionKernel V E)
    (hJC : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G)) :
    let H := temporaryLineNormalizer T V E
    let Q := (temporaryCore T V E).subgroupOf H
    letI : Q.Normal := temporaryCore_normal T V E
    ∃ (S : Sylow 2 H), (S : Subgroup H).map H.subtype = lineT T E ∧
      ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
        A ≤ (temporaryCentralizer T V E).subgroupOf H ∧
        A.map (QuotientGroup.mk' Q) ≠ ⊥ := by
  let H := temporaryLineNormalizer T V E
  let Q := (temporaryCore T V E).subgroupOf H
  let C := (temporaryCentralizer T V E).subgroupOf H
  let : Q.Normal := temporaryCore_normal T V E
  obtain ⟨S, hS⟩ := lineT_sylow_temporary T V E hEV P hP
  have hJC' : elementaryAbelianMaxJ (S : Subgroup H) ≤ C := by
    have hmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (lineT T E) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hS]
    intro x hx
    exact ⟨x.property, hJC (hmap ▸ mem_map_of_mem H.subtype hx)⟩
  have hJQ : ¬ elementaryAbelianMaxJ C ≤ Q := by
    intro h
    apply temporaryMaxJ_not_le_core M T V E hEV P hP hNM hI hcore
    have hm := map_mono (f := H.subtype) h
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (show temporaryCentralizer T V E ≤ H from inf_le_left),
      map_subgroupOf_eq_of_le (temporaryCore_le T V E)] at hm
    exact hm
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty (S : Subgroup H)
  obtain ⟨A, hA, hne⟩ := exists_max_nontrivial_image C Q S hJQ
    ⟨B, hB, (le_sSup hB).trans hJC'⟩
  exact ⟨S, hS, A, hA, (le_sSup hA).trans hJC', hne⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
