module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Centralizing
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Quotient preimages and the two normalizer exclusions

`starPreimage H K` is the ambient image of the full preimage of K in
H → H/O₂(H). Its image is exactly K, and normality is relative to H.
For normal K its intrinsic two-core has ambient image O₂(H), and its
intrinsic two-core quotient is actually isomorphic to K. Its two-residual
is characteristic, so H normalizes the embedded O² preimage. The source
bound N_G(L₀) ≤ M therefore excludes the residual L₀ case when applicable.

`seedSpace` is the actual quotient image of V₃ in U_H/V₁. Under V₁ ≤ V₃,
membership in that image lifts exactly to membership in V₃. If the normal
moved space equals this seed image, H normalizes V₃. Together with
H ≤ N_G(V₁), source 13.5.5 then gives H ≤ M.

The residual alternatives and moved-space equality must still be proved
from the marked A₆ or triple-cover geometry; they are not asserted here.
In particular the normalizer bound from 13.2.2(9) requires the triple-cover
case, which its caller must establish.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the last paragraph of 13.8.5, printed p.948 (PDF p.965), using
13.2.2(9), printed p.877, and 13.5.5, printed p.916.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable
variable {G : Type*} [Group G]

def starPreimage (H : Subgroup G) (K : Subgroup (Source.Hstar H)) : Subgroup G :=
  (K.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

theorem starPreimage_le (H : Subgroup G) (K : Subgroup (Source.Hstar H)) :
    starPreimage H K ≤ H := map_subtype_le _

theorem starPreimage_subgroupOf (H : Subgroup G) (K : Subgroup (Source.Hstar H)) :
    (starPreimage H K).subgroupOf H = K.comap (QuotientGroup.mk' (pCore 2 H)) := by
  ext h
  constructor
  · rintro ⟨k, hk, he⟩
    have he' : k = h := Subtype.ext he
    exact he' ▸ hk
  · intro hh
    exact ⟨h, hh, rfl⟩

theorem starImage_starPreimage (H : Subgroup G) (K : Subgroup (Source.Hstar H)) :
    Source.starImage H (starPreimage H K) = K := by
  rw [Source.starImage, starPreimage_subgroupOf,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

instance starPreimage_normal (H : Subgroup G) (K : Subgroup (Source.Hstar H)) [K.Normal] :
    ((starPreimage H K).subgroupOf H).Normal := by
  rw [starPreimage_subgroupOf]
  infer_instance

theorem le_normalizer_starPreimage (H : Subgroup G) (K : Subgroup (Source.Hstar H)) [K.Normal] :
    H ≤ normalizer (starPreimage H K : Set G) :=
  le_normalizer_of_normal_subgroupOf (starPreimage_le H K)

theorem core_le_starPreimage (H : Subgroup G) (K : Subgroup (Source.Hstar H)) :
    Source.QH H ≤ starPreimage H K := by
  rintro x ⟨h, hh, rfl⟩
  refine ⟨h, ?_, rfl⟩
  change QuotientGroup.mk' (pCore 2 H) h ∈ K
  have he : QuotientGroup.mk' (pCore 2 H) h = 1 := (QuotientGroup.eq_one_iff h).mpr hh
  rw [he]
  exact K.one_mem

theorem starPreimage_core (H : Subgroup G) (K : Subgroup (Source.Hstar H)) [K.Normal] :
    (starPreimage H K).pCoreIn 2 = Source.QH H := by
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes (starPreimage_le H K) (le_normalizer_starPreimage H K)
  · apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (core_le_starPreimage H K)
    exact (starPreimage_le H K).trans
      (le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))

/-- The intrinsic two-core quotient of the actual preimage is K*. -/
noncomputable def starPreimageQuotientEquiv [Finite G]
    (H : Subgroup G) (K : Subgroup (Source.Hstar H)) [K.Normal] :
    (starPreimage H K ⧸ pCore 2 (starPreimage H K)) ≃* K := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.comap q
  let e : starPreimage H K ≃* B :=
    (B.equivMapOfInjective H.subtype H.subtype_injective).symm
  let f := q.subgroupMap B
  have hker : f.ker = pCore 2 B := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : B.Normal).isSubnormal]
    change (q.subgroupMap B).ker = (pCore 2 H).subgroupOf B
    rw [ker_subgroupMap]
    rw [show q.ker = pCore 2 H from QuotientGroup.ker_mk' _]
  have hmap : B.map q = K := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective B)).trans
        (MulEquiv.subgroupCongr hmap)))

/-- The ambient image of the literal two-residual of the preimage. -/
def preimageResidual (H : Subgroup G) (K : Subgroup (Source.Hstar H)) : Subgroup G :=
  (pResidual 2 (starPreimage H K)).map (starPreimage H K).subtype

theorem le_normalizer_preimageResidual
    (H : Subgroup G) (K : Subgroup (Source.Hstar H)) [K.Normal] :
    H ≤ normalizer (preimageResidual H K : Set G) :=
  (le_normalizer_starPreimage H K).trans
    (normalizer_le_normalizer_characteristic_image _ _)

theorem le_M_of_preimageResidual_eq
    (H M L₀ : Subgroup G) (K : Subgroup (Source.Hstar H)) [K.Normal]
    (hres : preimageResidual H K = L₀) (hNM : normalizer (L₀ : Set G) ≤ M) : H ≤ M := by
  have hn := le_normalizer_preimageResidual H K
  rw [hres] at hn
  exact hn.trans hNM

variable {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The literal image V₃/V₁ in U_H/V₁, as a binary subspace. -/
def seedSpace (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)] :
    Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
    ((V₃.subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))))

theorem vector_mem_seedSpace_iff (hV : V₁ ≤ V₃) (u : Source.UH H V₃) :
    vector H V₃ V₁ u ∈ seedSpace H V₃ V₁ ↔ (u : G) ∈ V₃ := by
  change QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u ∈
    (V₃.subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))) ↔ _
  constructor
  · rintro ⟨v, hv, he⟩
    have he' : v / u ∈ V₁.subgroupOf (Source.UH H V₃) :=
      QuotientGroup.eq_iff_div_mem.mp he
    have hv' : (v : G) ∈ V₃ := hv
    have hdiff : (v : G) / (u : G) ∈ V₁ := he'
    have hmem := V₃.mul_mem (V₃.inv_mem (hV hdiff)) hv'
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
      mul_one] using hmem
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- A normal moved space equal to the actual flag image forces normalization
of V₃; the denominator containment is retained. -/
theorem le_normalizer_seed_of_movedSpace_eq
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ V₃)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (hmoved : subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁) :
    H ≤ normalizer (V₃ : Set G) := by
  apply le_normalizer_iff.mpr
  intro h hh v hv
  let u : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
  have hu : vector H V₃ V₁ u ∈ subspaceCommutator ρ ⊤ K := by
    rw [hmoved, vector_mem_seedSpace_iff hV]
    exact hv
  have hi : (⊤ : Subgroup (Source.Hstar H)) ≤
      subspaceStabilizer ρ (subspaceCommutator ρ ⊤ K) :=
    subspaceCommutator_invariant_normalizer ρ
      (by intro a _ w; simp) le_normalizer_of_normal
  have hw := (hi (mem_top (QuotientGroup.mk' (pCore 2 H) ⟨h, hh⟩)) _).2 hu
  rw [hρ, hmoved, vector_mem_seedSpace_iff hV] at hw
  exact hw

/-- The source 13.5.5 conclusion after establishing Ũ_K=Ṽ₃. -/
theorem le_M_of_movedSpace_eq
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ V₃)
    (M : Subgroup G) (hH₁ : H ≤ normalizer (V₁ : Set G))
    (h13_5_5 : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (hmoved : subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁) : H ≤ M :=
  (le_inf hH₁ (le_normalizer_seed_of_movedSpace_eq ρ hρ hV K hmoved)).trans h13_5_5

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable

end
