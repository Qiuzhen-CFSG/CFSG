module
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.SylowIndex
public import Theory.SpecificGroups.BinaryLinear.SixSectionCore
public import Theory.SpecificGroups.BinaryLinear.QuinticNormalizer
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# A6 sections of Sylow normalizer index at most two cannot occur in GL5(2)

A section with trivial two-core has normalizer two-subgroups of order at
most 32. Otherwise its nontrivial two-core has an endpoint parabolic as
normalizer. The Levi quotient is the actual A8, where the image A6 has
normalizer two-part at most sixteen. The parabolic two-core also has order
at most sixteen. Thus the original section normalizer meets any Sylow in
order at most 256, contradicting index at most two in a Sylow of order 1024.

The original preferred nonsingular-point consumer supplies precisely this
relative index bound. No full Sylow is assumed to normalize the section.
Source: Aschbacher--Smith 12.6.18, printed p.827, combined manuscript
of 1 March 2004; the endpoint geometry is that of A.3.12(5).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.QuinticNormalizer
open OuterCyclic
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private theorem end_quotient (H : Subgroup (LinearGroup 5))
    (hH : FiveParabolicStabilizer.IsEndParabolic H) :
    Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 8)) := by
  open FiveFlagGeometry FiveFlagGeometry.MaximalOvergroups in
    rcases hH with ⟨v,hv,rfl⟩ | ⟨f,hf,rfl⟩
    · obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace
        (Submodule.span (ZMod 2) {v}) 0 (by simpa using finrank_span_singleton hv)
      let e := MulEquiv.subgroupCongr ((flagStabilizer_singleton b 0).trans (congrArg parabolic hb))
      exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
        ((lineQuotientEquiv b).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)⟩
    · have hd : Module.finrank (ZMod 2) f.ker = 4 := by
        have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
        norm_num [Space] at hh
        omega
      obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace f.ker 3 (by simpa using hd)
      let e := MulEquiv.subgroupCongr ((flagStabilizer_singleton b 3).trans (congrArg parabolic hb))
      exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
        ((hyperplaneQuotientEquiv b).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)⟩

/-- The literal A6 two-core section cannot have Sylow normalizer index at most two. -/
theorem six_section_not_small_index (A : Subgroup (LinearGroup 5))
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 (LinearGroup 5))
    (hi : (normalizer (A : Set (LinearGroup 5))).relIndex S ≤ 2) : False := by
  let N := normalizer (A : Set (LinearGroup 5))
  let U := A.pCoreIn 2
  let H := normalizer (U : Set (LinearGroup 5))
  have h5 : 5 ∣ Nat.card A := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 A))
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hNH : N ≤ H := normalizer_le_normalizer_characteristic_image A (pCore 2 A)
  have hAH : A ≤ H := A.le_normalizer.trans hNH
  have hU : U ≠ ⊥ := by
    intro hh
    exact six_section_core_ne_bot A e S (hi.trans (by decide))
      ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hh)
  obtain ⟨b⟩ := end_quotient H
    (normalizer_isEndParabolic U (isPGroup_pCoreIn 2 A) hU (h5.trans (card_dvd_of_le hAH)))
  let q := b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective,QuotientGroup.ker_mk']
  have hker : IsPGroup 2 q.ker := hk.symm ▸ pCore_isPGroup
  let A₀ := A.subgroupOf H
  let a : A₀ ≃* A := subgroupOfEquivOfLe hAH
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  obtain ⟨a'⟩ := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.six_section_image
    q hker A₀ eA
  have hcore : Nat.card q.ker ≤ 16 := by
    have hHN : H ≤ normalizer (H.pCoreIn 2 : Set (LinearGroup 5)) :=
      H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hh := FiveTwoLocalFive.card_le_sixteen (H.pCoreIn 2) (isPGroup_pCoreIn 2 H)
      (h5.trans (card_dvd_of_le (hAH.trans hHN)))
    rw [pCoreIn,card_map_of_injective H.subtype_injective] at hh
    rwa [hk]
  let P := N ⊓ (S : Subgroup (LinearGroup 5))
  let E := P.subgroupOf H
  have hPH : P ≤ H := inf_le_left.trans hNH
  let c : E ≃* P := subgroupOfEquivOfLe hPH
  have hE : IsPGroup 2 E := (S.isPGroup'.to_le (show P ≤ S from inf_le_right)).comap_subtype
  have hn : E ≤ normalizer (A₀ : Set H) := by
    rw [←subgroupOf_normalizer_eq hAH]
    exact comap_mono inf_le_left
  have him : E.map q ≤ normalizer (A₀.map q : Set (alternatingGroup (Fin 8))) :=
    (map_mono hn).trans (le_normalizer_map q)
  have h720 : Nat.card (E.map q) ∣ 720 :=
    (card_dvd_of_le him).trans
      (Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.six_normalizer_card_dvd _ a')
  obtain ⟨R,hR⟩ := (hE.map q).exists_le_sylow
  have hRcard : Nat.card R = 64 := by
    have hh := AlternatingEight.sylow_image_card R
    rwa [card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective] at hh
  have h64 : Nat.card (E.map q) ∣ 64 := hRcard ▸ card_dvd_of_le hR
  have himcard : Nat.card (E.map q) ≤ 16 :=
    Nat.le_of_dvd (by decide : 0 < 16) (Nat.dvd_gcd h64 h720)
  let f := q.comp E.subtype
  have hfker : Nat.card f.ker ≤ 16 := by
    have hh : f.ker.map E.subtype ≤ q.ker := map_comap_le E.subtype q.ker
    have hb := card_le_of_le hh
    rw [card_map_of_injective E.subtype_injective] at hb
    exact hb.trans hcore
  have hr : f.range = E.map q := by
    rw [MonoidHom.range_comp,range_subtype]
  have hcount := f.ker.card_mul_index
  rw [index_ker,hr] at hcount
  have hPcard : Nat.card P ≤ 256 := by
    have hh := Nat.mul_le_mul hfker himcard
    rw [hcount,Nat.card_congr c.toEquiv] at hh
    exact hh
  have hS : Nat.card S = 1024 := by
    rw [S.card_eq_multiplicity]
    have hh : Nat.card (LinearGroup 5) = 9999360 := by
      rw [←Nat.card_congr (matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
      decide
    rw [hh]
    decide +kernel
  have hm : Nat.card P * N.relIndex S = 1024 := by
    simpa only [P,relIndex_bot_left,inf_relIndex_right,hS] using
      relIndex_mul_relIndex (⊥ : Subgroup (LinearGroup 5)) P (S : Subgroup _) bot_le inf_le_right
  have hh := Nat.mul_le_mul hPcard hi
  rw [hm] at hh
  norm_num at hh
end BinaryLinear.QuinticNormalizer
