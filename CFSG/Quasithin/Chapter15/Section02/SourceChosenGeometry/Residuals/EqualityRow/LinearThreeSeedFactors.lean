module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingSylow
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Factors

/-!
# Conjugate cubic factors from the original wreath residual

The actual H/O₂(H) wreath quotient makes T irreducible on K/O₂(K).
For a specified S-invariant normal cubic residual E of K, enlarge E by
O₂(K), conjugate by the original t outside S, and use irreducibility.
Taking O² recovers E and its literal conjugate, whose join is K.
These are the factors required by the canonical-seed instance of 15.2.22;
no partner residual identity or marked-factor recognition is assumed.

Source: Aschbacher--Smith, 15.2.21--22, printed pp.1114--1115,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_of_core_le {K L : Subgroup G}
    [IsMulCommutative (K ⧸ pCore 2 K)]
    (hQL : K.pCoreIn 2 ≤ L) (hLK : L ≤ K) :
    K ≤ normalizer (L : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 K)
  have hker : q.ker ≤ L.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hQL (mem_map_of_mem K.subtype hx)
  have hn : (L.subgroupOf K).Normal := by
    rw [← comap_map_eq_self hker]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer hLK).mp hn

private theorem sylow_isCoatom (H : Subgroup G) (S : Sylow 2 H)
    (e : (H ⧸ pCore 2 H) ≃* ChosenGeometry.Wreath) : IsCoatom (S : Subgroup H) := by
  let f := (e.trans ChosenGeometry.matrixWreathEquiv).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := (e.trans ChosenGeometry.matrixWreathEquiv).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change (e.trans ChosenGeometry.matrixWreathEquiv) (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ _
    rw [← (e.trans ChosenGeometry.matrixWreathEquiv).map_one,
      (e.trans ChosenGeometry.matrixWreathEquiv).injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hm := isCoatom_comap_of_surjective hf
    (wreath_two_sylow_isCoatom (S.mapSurjective hf))
  change IsCoatom (((S : Subgroup H).map f).comap f) at hm
  rwa [comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal S)] at hm

omit [Finite G] in
private theorem residual_sup_two (Y Q : Subgroup G) (hp : IsPPerfect 2 Y)
    (hq : IsPGroup 2 Q) (hn : Q ≤ normalizer (Y : Set G)) :
    (pResidual 2 (Y ⊔ Q : Subgroup G)).map (Y ⊔ Q).subtype = Y := by
  let D := Y ⊔ Q
  let : (Y.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer hn)
  have hp' : IsPPerfect 2 (Y.subgroupOf D) :=
    hp.of_surjective (subgroupOfEquivOfLe (show Y ≤ D from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show Y ≤ D from le_sup_left)).symm.surjective
  have hs : Y.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ D from le_sup_left) (show Q ≤ D from le_sup_right)]
    exact subgroupOf_self D
  rw [pResidual_eq_of_isPPerfect_sup (Y.subgroupOf D) (Q.subgroupOf D)
    hp' hq.comap_subtype hs, map_subgroupOf_eq_of_le (show Y ≤ D from le_sup_left)]

variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- The original Sylow action is irreducible, using the actual wreath quotient of H. -/
theorem sylow_irreducible :
    IsSmallActionIrreducible (T : Subgroup G) (smallActionK H) := by
  let K := smallActionK H
  let e := ChosenGeometry.residualQuotientEquiv H r.quotient.some
  let : IsElementaryAbelian 3 (K ⧸ pCore 2 K) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hKH : K ≤ H := map_subtype_le _
  have hTH : (T : Subgroup G) ≤ H := r.geometry.outside.1.1.2
  have hHK : H ≤ normalizer (K : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pResidual 2 H).le_normalizer_map H.subtype
  refine ⟨hTH.trans hHK, ?_⟩
  intro L hQL hLK hTL
  have hKL : K ≤ normalizer (L : Set G) := normalizes_of_core_le hQL hLK
  have hHL : H ≤ normalizer (L : Set G) := by
    rw [← r.residual_join]
    exact sup_le hKL hTL
  have hLH : L ≤ H := hLK.trans hKH
  let A := L.subgroupOf H
  let P := T.subtype hTH
  let : A.Normal := normal_subgroupOf_of_le_normalizer hHL
  by_cases hLP : L ≤ (T : Subgroup G)
  · left
    apply le_antisymm ?_ hQL
    exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hLP) hLK hKL
  · right
    have hgen : A ⊔ (P : Subgroup H) = ⊤ := by
      rcases (sylow_isCoatom H P r.quotient.some).le_iff.mp
        (show (P : Subgroup H) ≤ A ⊔ (P : Subgroup H) from le_sup_right) with he | he
      · exact he
      · exfalso
        apply hLP
        intro x hx
        have hm : (⟨x,hLH hx⟩ : H) ∈ (P : Subgroup H) := he ▸
          (show (⟨x,hLH hx⟩ : H) ∈ A ⊔ (P : Subgroup H) from
            (show A ≤ A ⊔ (P : Subgroup H) from le_sup_left)
              (show (⟨x,hLH hx⟩ : H) ∈ A from hx))
        exact hm
    have hKA : pResidual 2 H ≤ A := sInf_le ⟨inferInstance,
      isPGroup_quotient_of_sup_eq_top A (P : Subgroup H) P.isPGroup' hgen⟩
    exact le_antisymm hLK (by
      rintro _ ⟨x,hx,rfl⟩
      exact hKA hx)

/-- Start the constructed residual pair with a specified normal cubic factor.
The second factor is its literal t-conjugate, and irreducibility of T supplies
both generation and its distinctness from the first. -/
theorem residualPair_with_first (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    {Y : Subgroup G} (hY : Y ∈ normalCubicResiduals (smallActionK H))
    (hSY : smallActionS T (⁅V,B⁆ : Subgroup G) ≤ normalizer (Y : Set G))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T (⁅V,B⁆ : Subgroup G)) :
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T (⁅V,B⁆ : Subgroup G)) (smallActionK H) t,
      p.K₁ = Y := by
  let K := smallActionK H
  let S := smallActionS T (⁅V,B⁆ : Subgroup G)
  let Q := K.pCoreIn 2
  let L := Y ⊔ Q
  let f := (MulAut.conj t).toMonoidHom
  let L₂ := L.map f
  have hirr := r.sylow_irreducible
  have hKY : K ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hY.1).mp hY.2.1
  have hKQ : K ≤ normalizer (Q : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hKL : K ≤ normalizer (L : Set G) :=
    (le_inf hKY hKQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hLK : L ≤ K := sup_le hY.1 (pCoreIn_le 2 K)
  have hL₂K : L₂ ≤ K := (map_mono hLK).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hirr.1 ht))
  have hSL : S ≤ normalizer (L : Set G) :=
    (le_inf hSY ((inf_le_left.trans hirr.1).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTL : (T : Subgroup G) ≤ normalizer ((L ⊔ L₂ : Subgroup G) : Set G) := by
    simpa only [inv_inv] using index_two_normalizes_pair S (T : Subgroup G) L
      inf_le_left (r.escape_index hI).2 t⁻¹ ((T : Subgroup G).inv_mem ht)
      (by simpa only [inv_mem_iff] using htS) hSL
  have hspan : L ⊔ L₂ = K := by
    rcases hirr.2 (L ⊔ L₂) (le_sup_right.trans le_sup_left)
      (sup_le hLK hL₂K) hTL with he | he
    · have hp : IsPGroup 2 Y := (isPGroup_pCoreIn 2 K).to_le
        ((le_sup_left.trans le_sup_left).trans he.le)
      obtain ⟨n,hn⟩ := (hp.to_quotient (pCore 2 Y)).exists_card_eq
      rw [hY.2.2.2] at hn
      have hd : 3 ∣ 2 ^ n := by rw [← hn]
      exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
    · exact he
  have hKL₂ : K ≤ normalizer (L₂ : Set G) :=
    normalizes_conjugate_of_normalizes (hirr.1 ht) hKL
  let : (L.subgroupOf (L ⊔ L₂)).Normal :=
    normal_subgroupOf_of_le_normalizer (hspan ▸ hKL)
  let : (L₂.subgroupOf (L ⊔ L₂)).Normal :=
    normal_subgroupOf_of_le_normalizer (hspan ▸ hKL₂)
  have hres : (pResidual 2 L).map L.subtype = Y :=
    residual_sup_two Y Q hY.2.2.1 (isPGroup_pCoreIn 2 K) ((pCoreIn_le 2 K).trans hKY)
  have hres₂ : (pResidual 2 L₂).map L₂.subtype = Y.map f := by
    rw [← map_embedded_pResidual 2 L f, hres]
  have hYY : Y ⊔ Y.map f = K := by
    rw [← hres₂, ← hres, embedded_pResidual_sup_of_relative_normal, hspan,
      (pResidual_eq_top_iff 2 K).mpr (isPPerfect_embedded_pResidual 2 H),
      ← MonoidHom.range_eq_map, range_subtype]
  exact ⟨⟨Y,Y.map f,ht,htS,hY,
    normalCubicResiduals_conjugate K Y t (hirr.1 ht) hY,hYY,rfl,hSY⟩,rfl⟩


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
