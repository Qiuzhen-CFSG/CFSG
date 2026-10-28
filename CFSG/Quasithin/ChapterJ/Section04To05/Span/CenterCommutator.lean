module

public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Definitions
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The central line is the actual Sylow displacement on HC/U

The central line has index two in the normal four-group HC/U, so every
displacement lies in it. K acts trivially on HC/U and H=KT; if T also
acted trivially, HC/U would lie in the center of H/U, contradicting their
orders four and two. Thus the T-displacements are exactly the central line.
Taking full preimages gives Q₀=U[HC,T], on the original quotient map.

Source: the Q₀ step in Aschbacher–Smith J.4.3(2), printed p.441.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

private theorem hat_surjective : Function.Surjective (hatMap d) :=
  QuotientGroup.mk'_surjective _

private theorem hat_H : hat d d.toTypeRuSetup.H = ⊤ := by
  rw [hat,subgroupOf_self,← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top_of_surjective _ (hat_surjective d)

/-- The actual residual and selected Sylow images generate the entire H/U. -/
theorem hat_K_sup_hat_T :
    hat d d.toTypeRuSetup.K ⊔ hat d (d.T : Subgroup G) = ⊤ := by
  have h := congrArg (fun A : Subgroup d.toTypeRuSetup.H =>
    A.map d.toTypeRuSetup.H.subtype)
    (pResidual_sup_sylow_eq_top (d.T.subtype d.toTypeRuSetup.T_le_H))
  rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype] at h
  change d.toTypeRuSetup.K ⊔
    ((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = _ at h
  rw [map_subgroupOf_eq_of_le d.toTypeRuSetup.T_le_H] at h
  rw [← hat_sup d d.toTypeRuSetup.K_le_H d.toTypeRuSetup.T_le_H,h,hat_H]

/-- The original fixed four-group in H/U has order four. -/
theorem hat_HC_card : Nat.card (hat d d.toTypeRuSetup.HC) = 4 := by
  have h := hat_card d d.toTypeRuSetup.HC inf_le_left
  rw [inf_eq_right.mpr d.U_le_HC,d.ru2.card_U d.card_Z,d.card_HC] at h
  omega

private theorem hat_HC_normal : (hat d d.toTypeRuSetup.HC).Normal := by
  let : (d.toTypeRuSetup.HC.subgroupOf d.toTypeRuSetup.H).Normal := d.toTypeRuSetup.HC_normal
  exact Subgroup.Normal.map inferInstance (hatMap d) (hat_surjective d)

/-- K fixes the actual HC/U pointwise. -/
theorem hat_K_centralizes_HC :
    hat d d.toTypeRuSetup.K ≤ centralizer (hat d d.toTypeRuSetup.HC : Set (Hat d)) := by
  rintro x ⟨k,hk,rfl⟩ y ⟨q,hq,rfl⟩
  have hc := d.HC_commutator_K_mem_U ⟨q,hq⟩ ⟨k,hk⟩
  have hh := (hatMap_eq_one d ⁅k,q⁆).mpr hc
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
  exact hh.symm

/-- The source identity Q̂₀=[ĤC,T̂], with both literal quotient images. -/
theorem hat_HC_T_commutator :
    ⁅hat d d.toTypeRuSetup.HC,hat d (d.T : Subgroup G)⁆ = center (Hat d) := by
  let C := hat d d.toTypeRuSetup.HC
  let Z := center (Hat d)
  let : C.Normal := hat_HC_normal d
  have hz : Z ≤ C := by
    change center (Hat d) ≤ hat d d.toTypeRuSetup.HC
    rw [← hat_Q₀]
    exact hat_mono d (Q₀_le_HC d)
  have hi : Z.relIndex C = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (Hat d)) Z C bot_le hz
    simp only [relIndex_bot_left] at hh
    change Nat.card Z * Z.relIndex C = Nat.card C at hh
    rw [center_hat_card d,hat_HC_card d] at hh
    omega
  have hle : ⁅C,hat d (d.T : Subgroup G)⁆ ≤ Z :=
    commutator_le_of_normalized_index_two C Z _ hz hi
      le_normalizer_of_normal le_normalizer_of_normal
  have hn : ⁅C,hat d (d.T : Subgroup G)⁆ ≠ ⊥ := by
    intro he
    have ht : hat d (d.T : Subgroup G) ≤ centralizer (C : Set (Hat d)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hall : (⊤ : Subgroup (Hat d)) ≤ centralizer (C : Set (Hat d)) := by
      rw [← hat_K_sup_hat_T d]
      exact sup_le (hat_K_centralizes_HC d) ht
    have hc : C ≤ center (Hat d) := by
      have hh := le_centralizer_iff.mp hall
      simpa only [coe_top,centralizer_univ] using hh
    have hh := card_le_of_le hc
    rw [hat_HC_card d,center_hat_card d] at hh
    omega
  apply eq_of_le_of_card_ge hle
  let : Nontrivial (⁅C,hat d (d.T : Subgroup G)⁆ : Subgroup (Hat d)) :=
    (nontrivial_iff_ne_bot _).mpr hn
  have hh := Finite.one_lt_card (α := (⁅C,hat d (d.T : Subgroup G)⁆ : Subgroup (Hat d)))
  rw [center_hat_card d]
  omega

private theorem eq_of_hat_eq {A B : Subgroup G}
    (hAH : A ≤ d.toTypeRuSetup.H) (hBH : B ≤ d.toTypeRuSetup.H)
    (hUA : d.toTypeRuSetup.U ≤ A) (hUB : d.toTypeRuSetup.U ≤ B)
    (he : hat d A = hat d B) : A = B := by
  have h := congrArg (fun C : Subgroup (Hat d) => C.comap (hatMap d)) he
  change ((A.subgroupOf d.toTypeRuSetup.H).map (hatMap d)).comap (hatMap d) =
    ((B.subgroupOf d.toTypeRuSetup.H).map (hatMap d)).comap (hatMap d) at h
  rw [comap_map_eq,comap_map_eq] at h
  have hker : (hatMap d).ker = d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H :=
    QuotientGroup.ker_mk' _
  rw [hker,sup_eq_left.mpr (subgroupOf_mono _ hUA),sup_eq_left.mpr (subgroupOf_mono _ hUB)] at h
  have hm := congrArg (fun C : Subgroup d.toTypeRuSetup.H => C.map d.toTypeRuSetup.H.subtype) h
  rwa [map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hBH] at hm

/-- The full preimage form used to place Q₀ in S₂. -/
theorem Q₀_eq_U_sup_commutator_HC_T :
    Q₀ d = d.toTypeRuSetup.U ⊔ ⁅d.toTypeRuSetup.HC,(d.T : Subgroup G)⁆ := by
  have hc : ⁅d.toTypeRuSetup.HC,(d.T : Subgroup G)⁆ ≤ d.toTypeRuSetup.H :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le inf_le_left d.toTypeRuSetup.T_le_H)
  apply eq_of_hat_eq d (Q₀_le_H d) (sup_le d.ru2.natural.section_le hc)
    (U_le_Q₀ d) le_sup_left
  rw [hat_sup d d.ru2.natural.section_le hc,hat_commutator d inf_le_left
    d.toTypeRuSetup.T_le_H,hat_HC_T_commutator,hat_Q₀]
  have hu : hat d d.toTypeRuSetup.U = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro u hu
    exact (hatMap_eq_one d u).mpr hu
  simp only [hu,bot_sup_eq]

end CFSG.Quasithin.ChapterJ.RuSubgroup
