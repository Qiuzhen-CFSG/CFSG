module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Algebra
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.Residuals

/-!
# Identifying and generating the plane residuals

A relatively normal two-perfect supplement to a two-group is the exact
ambient two-residual. Equality of images in the actual two-core quotient
provides the needed supplement. Two relatively normal two-perfect factors
whose images generate that quotient generate Y itself, including the literal
set product. These lemmas support identification of Y_L and Y_D from the
natural two-plane action; they do not assume that identification.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

-- The ambient residual is exactly its p-perfect supplement of a two-group.
theorem residual_eq_of_two_supplement {C A Q : Subgroup G}
    (hAC : A ≤ C) (hQC : Q ≤ C) (hCA : C ≤ normalizer (A : Set G))
    (hA : IsPPerfect 2 A) (hQ : IsPGroup 2 Q) (hgen : A ⊔ Q = C) :
    Stellmacher.twoResidualAmbient C = A := by
  let A' := A.subgroupOf C
  let : A'.Normal := normal_subgroupOf_of_le_normalizer hCA
  have hpA : IsPPerfect 2 A' := hA.of_surjective
    (subgroupOfEquivOfLe hAC).symm.toMonoidHom (subgroupOfEquivOfLe hAC).symm.surjective
  have he := pResidual_eq_of_isPPerfect_sup A' (Q.subgroupOf C) hpA hQ.comap_subtype (by
    rw [← subgroupOf_sup hAC hQC, hgen, subgroupOf_self])
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual, he,
    map_subgroupOf_eq_of_le hAC]

omit [Finite G] in
theorem image_eq_of_same_core_supplement {Y A C : Subgroup G}
    (hAC : A ≤ C) (hCY : C ≤ Y)
    (he : (A.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) =
      (C.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)))
    (hQC : Y.pCoreIn 2 ≤ C) : A ⊔ Y.pCoreIn 2 = C := by
  have h := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 Y))) he
  rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at h
  have hm := congrArg (Subgroup.map Y.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le (hAC.trans hCY),
    map_subgroupOf_eq_of_le hCY] at hm
  exact hm.trans (sup_eq_left.mpr hQC)

theorem generated_of_images {Y A D : Subgroup G}
    (hAY : A ≤ Y) (hDY : D ≤ Y)
    (hYA : Y ≤ normalizer (A : Set G)) (hYD : Y ≤ normalizer (D : Set G))
    (hY : IsPPerfect 2 Y) (hA : IsPPerfect 2 A) (hD : IsPPerfect 2 D)
    (himages : ((A ⊔ D).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) = ⊤) :
    Y = A ⊔ D ∧ (Y : Set G) = (A : Set G) * (D : Set G) := by
  have hgen : (A ⊔ D) ⊔ Y.pCoreIn 2 = Y := by
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 Y))) himages
    rw [comap_map_eq, comap_top, QuotientGroup.ker_mk'] at h
    have hm := congrArg (Subgroup.map Y.subtype) h
    simpa only [pCoreIn, Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hAY hDY),
      ← MonoidHom.range_eq_map, range_subtype] using hm
  have hADperfect : IsPPerfect 2 (A ⊔ D : Subgroup G) := by
    rw [← pResidual_eq_top_iff]
    apply top_unique
    rw [← subgroupOf_self (A ⊔ D), subgroupOf_sup le_sup_left le_sup_right]
    apply sup_le
    · exact le_pResidual_of_isPPerfect _ (hA.of_surjective
        (subgroupOfEquivOfLe (show A ≤ A ⊔ D from le_sup_left)).symm.toMonoidHom
        (subgroupOfEquivOfLe (show A ≤ A ⊔ D from le_sup_left)).symm.surjective)
    · exact le_pResidual_of_isPPerfect _ (hD.of_surjective
        (subgroupOfEquivOfLe (show D ≤ A ⊔ D from le_sup_right)).symm.toMonoidHom
        (subgroupOfEquivOfLe (show D ≤ A ⊔ D from le_sup_right)).symm.surjective)
  have hres := residual_eq_of_two_supplement (sup_le hAY hDY) (pCoreIn_le 2 Y)
    ((le_inf hYA hYD).trans (normalizer_inf_normalizer_le_normalizer_sup A D))
    hADperfect (isPGroup_pCoreIn 2 Y) hgen
  have htop : Stellmacher.twoResidualAmbient Y = Y := by
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual,
      (pResidual_eq_top_iff 2 Y).mpr hY, ← MonoidHom.range_eq_map, range_subtype]
  have he := htop.symm.trans hres
  exact ⟨he, by rw [he, coe_mul_of_right_le_normalizer_left A D (hDY.trans hYA)]⟩

/-- The two equal conjugate cores exhaust the two-core of their product. -/
theorem core_of_residual_product {Y A D Q : Subgroup G}
    (hgen : Y = A ⊔ D) (hDA : D ≤ normalizer (A : Set G))
    (hA : A.pCoreIn 2 = Q) (hD : D.pCoreIn 2 = Q)
    (hcardD : Nat.card D = Nat.card A)
    (hAQ : Nat.card (A ⧸ pCore 2 A) = 3)
    (hYQ : Nat.card (Y ⧸ pCore 2 Y) = 9) : Y.pCoreIn 2 = Q := by
  have hYA : Y ≤ normalizer (A : Set G) := by
    rw [hgen]
    exact sup_le A.le_normalizer hDA
  have hQY : Q ≤ Y.pCoreIn 2 := by
    rw [← hA]
    exact pCoreIn_mono_of_normalizes (hgen ▸ le_sup_left) hYA
  have hcA : Nat.card A = Nat.card Q * 3 := by
    have h := (pCore 2 A).card_mul_index
    rw [index_eq_card, hAQ] at h
    have hc : Nat.card (pCore 2 A) = Nat.card Q := by
      rw [← hA, pCoreIn, card_map_of_injective A.subtype_injective]
    exact h.symm.trans (congrArg (fun n => n * 3) hc)
  have hcY : Nat.card Y = Nat.card (Y.pCoreIn 2) * 9 := by
    rw [pCoreIn, card_map_of_injective Y.subtype_injective]
    exact (pCore 2 Y).card_mul_index.symm.trans (by rw [index_eq_card, hYQ])
  have hInf : Nat.card Q ≤ Nat.card (A ⊓ D : Subgroup G) :=
    card_le_of_le (le_inf (hA ▸ pCoreIn_le 2 A) (hD ▸ pCoreIn_le 2 D))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A D hDA
  rw [← hgen] at hprod
  have hbound : Nat.card Q * Nat.card Y ≤ Nat.card A * Nat.card D :=
    (Nat.mul_le_mul_right (Nat.card Y) hInf).trans_eq hprod.symm
  rw [hcardD, hcA, hcY] at hbound
  have hcancel : Nat.card Q * Nat.card (Y.pCoreIn 2) ≤ Nat.card Q * Nat.card Q := by
    nlinarith
  have hsmall := Nat.le_of_mul_le_mul_left hcancel (Nat.card_pos (α := Q))
  exact (eq_of_le_of_card_ge hQY hsmall).symm

theorem planeResidual_map (M Y W : Subgroup G) (e : G ≃* G) :
    (planeResidual M Y W).map e.toMonoidHom =
      planeResidual (M.map e.toMonoidHom) (Y.map e.toMonoidHom) (W.map e.toMonoidHom) := by
  unfold planeResidual
  rw [map_twoResidualAmbient_of_subgroup_image _ _ _ rfl,
    map_inf _ _ _ e.injective, map_inf _ _ _ e.injective, Theory.Quasithin.map_centralizer]

omit [Finite G] in
theorem planeResidual_le (M Y W : Subgroup G) :
    planeResidual M Y W ≤ Y ⊓ (M ⊓ centralizer (W : Set G)) := map_subtype_le _

theorem normalizes_planeResidual {M Y W X : Subgroup G}
    (hXM : X ≤ normalizer (M : Set G)) (hXY : X ≤ normalizer (Y : Set G))
    (hXW : X ≤ normalizer (W : Set G)) :
    X ≤ normalizer (planeResidual M Y W : Set G) := by
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hM : M.map (MulAut.conj x).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (hXM hx)
  have hY : Y.map (MulAut.conj x).toMonoidHom = Y :=
    mem_normalizer_iff_map_conj_eq.mp (hXY hx)
  have hW : W.map (MulAut.conj x).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (hXW hx)
  have hm := planeResidual_map M Y W (MulAut.conj x)
  rw [hM, hY, hW] at hm
  exact hm

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
