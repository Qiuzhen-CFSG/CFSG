module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarMixedLeft
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.PCoreSupplementQuotient

/-!
# The original left parabolic in the mixed 6.1.5 argument

The left local group is literally L Baum(T). The Sylow subgroup normalizes
both factors, so this group is normal in LT. Characteristic two passes from
the original maximal two-local through LT to this normal subgroup.

The previously proved Baumann cover places it in L O₂(LT). Restriction of
the two-core then shows that L supplements its own two-core. This gives the
quotient identification by the original inclusion, before any rank-two
recognition. The actual left Hall has the required Borel and normalization
properties. The earlier natural fixed quotient and the separate right-factor
selection in 6.1.5 remain independent source duties.

Source: Aschbacher--Smith, 6.1.5, printed pp.666--667.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The actual left parabolic is normal in LT and has characteristic two. -/
theorem mixed_left_normal_characteristic :
    ((L ⊔ ChapterB.baumann (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal ∧
    generalizedFitting (L ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) =
      pCore 2 (L ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) := by
  let P := L ⊔ ChapterB.baumann (T : Subgroup G)
  let J := L ⊔ (T : Subgroup G)
  have hPJ : P ≤ J := sup_le_sup_left inf_le_left L
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (le_inf h.sylow_normalizes_L
      ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJP : J ≤ normalizer (P : Set G) :=
    sup_le (le_sup_left.trans P.le_normalizer) hTP
  let hPN : (P.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPJ).mpr hJP
  refine ⟨hPN, ?_⟩
  let := hPN
  have hJM : J ≤ M := sup_le h.L_le h.sylow_le
  have hM := h.simpleQTKE.evenCharacteristic T M h.maximal h.sylow_le
  have hJ := centralizer_pCore_le_of_sylow_le (T.subtype h.sylow_le)
    (J.subgroupOf M) (fun _ hx => (show (T : Subgroup G) ≤ J from le_sup_right) hx) hM
  have hcJ := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hJM)).mp hJ
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hPJ)).mp
      (normal_core_selfCentralizing hcJ (P.subgroupOf J)))

/-- The literal inclusion of L identifies the two original two-core quotients.
No quotient or component marking is reselected. -/
theorem mixed_left_quotient_of_natural_quotient
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ∃ e : (L ⧸ pCore 2 L) ≃*
      ((L ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (L ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G)),
      ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) =
        QuotientGroup.mk' (pCore 2 (L ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G))
          (inclusion le_sup_left l) := by
  let S := ChapterB.baumann (T : Subgroup G)
  let J := L ⊔ (T : Subgroup G)
  let P := L ⊔ S
  have hPJ : P ≤ J := sup_le_sup_left inf_le_left L
  have hSQ := ((h.rankOneInput hout).baumann_cover_of_natural_quotient
    (h.maximal_eq_normalizer_L ▸ hH) hm hZH).1
  have hPQ : P ≤ L ⊔ J.pCoreIn 2 :=
    sup_le le_sup_left (hSQ.trans (sup_le_sup_right inf_le_right _))
  have hLQ : L ≤ normalizer (J.pCoreIn 2 : Set G) :=
    (show L ≤ J from le_sup_left).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hcover : L ⊔ P.pCoreIn 2 = P := by
    apply le_antisymm (sup_le le_sup_left (pCoreIn_le 2 P))
    intro x hx
    have hxQ : x ∈ (L : Set G) * (J.pCoreIn 2 : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right L (J.pCoreIn 2) hLQ]
      exact hPQ hx
    obtain ⟨l, hl, q, hq, he⟩ := hxQ
    have hqP : q ∈ P := by
      have hh := P.mul_mem (P.inv_mem (mem_sup_left hl)) hx
      rw [← he, inv_mul_cancel_left] at hh
      exact hh
    rw [← he]
    exact (L ⊔ P.pCoreIn 2).mul_mem (mem_sup_left hl)
      (mem_sup_right (inf_pCoreIn_le_of_le 2 hPJ ⟨hqP, hq⟩))
  exact exists_pCoreQuotientEquiv_of_supplement (p := 2) (show L ≤ P from le_sup_left) hcover

/-- All left local fields of the mixed F.1.1 application, on the original
Baumann subgroup and one actual Hall of the original local Borel. -/
theorem mixed_left_source_of_natural_quotient
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    let S := ChapterB.baumann (T : Subgroup G)
    Chapter1.IsSylowIn 2 S (L ⊔ S) ∧
      ClassicalGroup.IsPSL ((L ⊔ S : Subgroup G) ⧸ pCore 2 (L ⊔ S : Subgroup G))
        2 (2 ^ n) ∧
      generalizedFitting (L ⊔ S : Subgroup G) = pCore 2 (L ⊔ S : Subgroup G) ∧
      ∃ D : Subgroup G, D ≤ RankOneGeneric.localBorel T L ∧
        IsHallSubgroup OddHall.oddPrimes (D.subgroupOf (RankOneGeneric.localBorel T L)) ∧
        (D : Set G) * (T : Set G) = (T : Set G) * (D : Set G) ∧
        D ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
        D ⊔ H ∈ Chapter1.HOver G (T : Set G) ∧
        D ≤ normalizer (S : Set G) ∧
        ChapterF.Source.borel (L ⊔ S) S = S ⊔ D := by
  let hi := h.rankOneInput hout
  have hH' := h.maximal_eq_normalizer_L ▸ hH
  have hSyl := hi.baumann_sylow_of_natural_quotient hH' hm hZH
  obtain ⟨e, _⟩ := h.mixed_left_quotient_of_natural_quotient hout hH hm hZH
  refine ⟨hSyl, h.quotient_model.of_mulEquiv e.symm,
    h.mixed_left_normal_characteristic.2, ?_⟩
  obtain ⟨D, hD, hHall, hperm, hfaith, hDH⟩ :=
    h.exists_hstar_left_cartan_overgroup hout hH hm hZH
  have hDS := hD.trans (hi.baumann_cover_of_natural_quotient hH' hm hZH).2
  exact ⟨D, hD, hHall, hperm, hfaith, hDH, hDS,
    mixed_left_borel_of_sylow_and_hall T L _ D h.sylow_normalizes_L inf_le_left
      hSyl hD hHall hDS⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
