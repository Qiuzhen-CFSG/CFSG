module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups.DicksonReduction
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.ElementaryNormalizerThreeRank
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# Excluding an S₄ inner intersection in square degree

The characteristic two-core of an S₄ intersection is a four-group normal
in the original overgroup. Every four-group in odd PGL₂ is self-centralizing,
so its normalizer has order dividing 4·|Aut(V₄)| = 24. An overgroup of an
ambient Sylow two-subgroup in square degree has order divisible by sixteen.
These divisibilities are incompatible. No maximality assumption is needed.

Source: the Dickson auxiliary calculation for Aschbacher--Smith E.1.14(6),
printed p.214, citing Aschbacher (1982), Lemma 4.10.
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups

open Subgroup GorensteinWalter
open PrimeGeometry.Diagonal.MaximalOvergroups

variable {F : Type*} [Field F] [Finite F]

local instance finitePGL : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- A normal S₄ intersection would give a normal self-centralizing
four-group in an overgroup whose order is divisible by sixteen. -/
public theorem inner_not_symmetric_four {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M) :
    ¬ Nonempty (inner M ≃* Equiv.Perm (Fin 4)) := by
  rintro ⟨e⟩
  have hF := oddPrimePower_of_square_card hpodd hFcard
  let N := innerIn M
  let : N.Normal := innerIn_normal hF M
  let eN : N ≃* Equiv.Perm (Fin 4) := (innerEquiv M).symm.trans e
  have hNc : Nat.card N = 24 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  obtain ⟨hE, hcases⟩ := symmetric_four_model_twoCore_data (Or.inl ⟨eN⟩)
  let : IsElementaryAbelian 2 (pCore 2 N) := hE
  have hfour : Nat.card (pCore 2 N) = 4 := by rcases hcases with h | h <;> omega
  let U : Subgroup M := (pCore 2 N).map N.subtype
  let : U.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map N.subtype
  let V : Subgroup (PGL2 F) := U.map M.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map M.subtype
  have hVc : Nat.card V = 4 := by
    rw [Nat.card_congr (U.equivMapOfInjective M.subtype M.subtype_injective).symm.toEquiv,
      Nat.card_congr ((pCore 2 N).equivMapOfInjective N.subtype N.subtype_injective).symm.toEquiv]
    exact hfour
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour V := ⟨hVc, IsElementaryAbelian.exponent_eq_prime⟩
  have hMV : M ≤ normalizer (V : Set (PGL2 F)) := by
    have h := Subgroup.le_normalizer_map (H := U) M.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      M.range_subtype] using h
  have hNdvd := V.card_normalizer_dvd_card_centralizer_mul_card_mulAut
  rw [pgl2_kleinFour_centralizer_eq_self F hF V inferInstance, hVc,
    IsKleinFour.card_mulAut V] at hNdvd
  have h16M : 16 ∣ Nat.card M :=
    (T.pow_dvd_card_of_pow_dvd_card
      (show 2 ^ 4 ∣ Nat.card (PGL2 F) from sixteen_dvd_pgl_card hpodd hFcard)).trans
        (Subgroup.card_dvd_of_le hTM)
  have hbad := h16M.trans ((Subgroup.card_dvd_of_le hMV).trans hNdvd)
  norm_num at hbad


end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups
