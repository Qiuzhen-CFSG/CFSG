module

public import Theory.GroupAction.NormalTwoSubgroupInversion
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Core
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Frattini.PGroup

/-!
# Inverting the actual plane modulo the two-core

Source: Aschbacher–Smith, Lemma 8.2.7, printed p.718 (PDF p.735).

The Sylow complement embeds in H/O₂(H). Its elementary structure removes
its Frattini subgroup, so the Chapter 1 irreducibility statement makes its
image a minimal normal subgroup. When H=XT, its image equals that of X.
The pair-core intersection and k=1 identify the image of V as an actual
order-two subgroup. Its T-normalization and the trivial two-core of the
quotient give inversion. The chosen quotient element is lifted back to V;
no normalization of the original Sylow complement by that lift is used.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- The elementary plane image is a minimal normal subgroup, as follows
from the existing irreducibility on its actual Frattini quotient. -/
theorem quotient_plane_minimal {p : ℕ} [Fact p.Prime] {T X Y H : Subgroup G}
    (h : LocalInput p T X Y H) [IsElementaryAbelian p Y]
    (D : Subgroup (XiQuotient H)) (hDA : D ≤ quotientImage H Y) [D.Normal] :
    D = ⊥ ∨ D = quotientImage H Y := by
  let A := quotientImage H Y
  let e := h.quotientComplementEquiv
  let _ : IsElementaryAbelian p A := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let _ : Fact (IsPGroup p A) := ⟨IsElementaryAbelian.isPGroup p A⟩
  let q := QuotientGroup.mk' (frattini A)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk', frattini_eq_bot_of_isElementaryAbelian (p := p)]
  let B := (D.subgroupOf A).map q
  have hB : ∀ s : normalizer (A : Set (XiQuotient H)), ∀ a ∈ B,
      frattiniConjugationAction _ _ le_rfl s a ∈ B := by
    intro s a ha
    obtain ⟨d, hd, rfl⟩ := ha
    rw [frattiniConjugationAction, MonoidHom.comp_apply, quotientAut_apply_mk]
    apply mem_map_of_mem
    change (s : XiQuotient H) * (d : XiQuotient H) * (s : XiQuotient H)⁻¹ ∈ D
    exact Subgroup.Normal.conj_mem (show D.Normal from inferInstance)
      (d : XiQuotient H) hd (s : XiQuotient H)
  rcases h.quotient_normalizer_irreducible B hB with hb | ht
  · left
    apply bot_unique
    intro d hd
    have hm : q ⟨d, hDA hd⟩ ∈ B := mem_map_of_mem q hd
    have he : q ⟨d, hDA hd⟩ = q 1 := by simpa [hb] using hm
    exact congrArg Subtype.val (hq he)
  · right
    apply le_antisymm hDA
    intro a ha
    have hm : q ⟨a, ha⟩ ∈ B := ht ▸ mem_top _
    obtain ⟨d, hd, he⟩ := hm
    have heq : d = ⟨a, ha⟩ := hq he
    change (d : XiQuotient H) ∈ D at hd
    simpa only [heq] using hd

omit [Finite G] in
/-- Ambient normalization descends along the actual quotient map. -/
theorem quotientImage_normalizes (H A B : Subgroup G)
    (hn : A ≤ normalizer (B : Set G)) :
    quotientImage H A ≤ normalizer (quotientImage H B : Set (XiQuotient H)) := by
  apply (map_mono ?_).trans ((B.subgroupOf H).le_normalizer_map _)
  exact (comap_mono hn).trans ((B.le_normalizer_comap H.subtype))

omit [Finite G] in
/-- The complement and X have the same quotient image when X is normal in H. -/
theorem quotientImage_plane_eq {p : ℕ} {T X Y H : Subgroup G}
    (h : LocalInput p T X Y H) (hHX : H ≤ normalizer (X : Set G)) :
    quotientImage H Y = quotientImage H X := by
  have hXH : X ≤ H := le_sup_left.trans h.overgroup
  have hc : X.pCoreIn 2 ≤ H.pCoreIn 2 := pCoreIn_mono_of_normalizes hXH hHX
  have hQ : quotientImage H (X.pCoreIn 2) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    obtain ⟨z, hz, he⟩ := hc hx
    have heq : z = x := Subtype.ext he
    change QuotientGroup.mk' (pCore 2 H) x = 1
    exact (QuotientGroup.eq_one_iff _).mpr (heq ▸ hz)
  have hsup : (X.pCoreIn 2 ⊔ Y).subgroupOf H =
      (X.pCoreIn 2).subgroupOf H ⊔ Y.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXH),
      map_subgroupOf_eq_of_le h.complement_le,
      map_subgroupOf_eq_of_le (h.complement.le.trans hXH)]
  change (Y.subgroupOf H).map _ = (X.subgroupOf H).map _
  rw [← h.complement, hsup, Subgroup.map_sup]
  change quotientImage H Y = quotientImage H (X.pCoreIn 2) ⊔ quotientImage H Y
  rw [hQ, bot_sup_eq]

omit [Finite G] in
/-- The quotient image of V has the source rank-one cardinality. -/
theorem quotientImage_card_two (I H V : Subgroup G)
    (hIH : I ≤ H) (hVI : V ≤ I) (hP : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2) :
    Nat.card (quotientImage H V) = 2 := by
  have hh : (V ⊓ H.pCoreIn 2).relIndex V = 2 := by
    rw [← pair_core_intersection I H V hIH hVI hP]
    exact hk
  rw [inf_relIndex_left] at hh
  change Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  have hm := relIndex_map_map_of_injective (pCore 2 H) (V.subgroupOf H) H.subtype_injective
  rw [map_subgroupOf_eq_of_le (hVI.trans hIH)] at hm
  exact hm ▸ hh
end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic Chapter 1 configuration and the literal pair kernel
supply an inverter modulo O₂(H), lifted from its normal order-two image. -/
theorem exists_inverter_of_localInput {p : ℕ} [Fact p.Prime] {T X Y H I V : Subgroup G}
    (h : LocalInput p T X Y H) [IsElementaryAbelian p Y]
    (hH : X ⊔ T = H) (hTV : T ≤ normalizer (V : Set G))
    (hIH : I ≤ H) (hVI : V ≤ I) (hP : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2) :
    ∃ v : V, ∀ y ∈ Y, (v : G) * y * (v : G)⁻¹ * y ∈ H.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := quotientImage H Y
  have hXH : X ≤ H := le_sup_left.trans hH.le
  have hTH : T ≤ H := le_sup_right.trans hH.le
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [← hH]
    exact sup_le X.le_normalizer h.invariant
  have hAX : A = quotientImage H X := quotientImage_plane_eq h hHX
  let _ : (X.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHX
  let _ : A.Normal := by
    rw [hAX]
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let _ : IsElementaryAbelian p A :=
    IsElementaryAbelian.of_surjective h.quotientComplementEquiv.toMonoidHom
      h.quotientComplementEquiv.surjective
  have hgen : A ⊔ quotientImage H T = ⊤ := by
    have hsub : X.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXH, map_subgroupOf_eq_of_le hTH,
        ← MonoidHom.range_eq_map, H.range_subtype, hH]
    rw [hAX, quotientImage, quotientImage, ← Subgroup.map_sup, hsub,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hirr : ∀ D : Subgroup (XiQuotient H), D ≤ A →
      quotientImage H T ≤ normalizer (D : Set (XiQuotient H)) → D = ⊥ ∨ D = A := by
    intro D hDA hTD
    have hAD : A ≤ centralizer (D : Set (XiQuotient H)) := by
      intro a ha
      apply mem_centralizer_iff.mpr
      intro d hd
      exact congrArg Subtype.val (mul_comm (⟨d, hDA hd⟩ : A) ⟨a, ha⟩)
    have hND : (⊤ : Subgroup (XiQuotient H)) ≤ normalizer (D : Set (XiQuotient H)) := by
      rw [← hgen]
      exact sup_le (hAD.trans (Subgroup.centralizer_le_normalizer _)) hTD
    let _ : D.Normal := normalizer_eq_top_iff.mp (top_unique hND)
    exact quotient_plane_minimal h D hDA
  obtain ⟨vbar, hvbar⟩ := Subgroup.exists_inverter_of_card_two A (quotientImage H T) (quotientImage H V)
    hgen (quotientImage_normalizes H T V hTV)
    (quotientImage_card_two I H V hIH hVI hP hk) (pCore_quotient_pCore_eq_bot 2) hirr
  obtain ⟨v, hvV, hqv⟩ := vbar.property
  refine ⟨⟨v, hvV⟩, ?_⟩
  intro y hy
  let yH : H := ⟨y, h.complement_le hy⟩
  have hyA : q yH ∈ A := mem_map_of_mem q hy
  have he := hvbar (q yH) hyA
  rw [← hqv] at he
  have herr : q (v * yH * v⁻¹ * yH) = 1 := by
    simp only [map_mul, map_inv]
    rw [he, inv_mul_cancel]
  exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp herr)
end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
