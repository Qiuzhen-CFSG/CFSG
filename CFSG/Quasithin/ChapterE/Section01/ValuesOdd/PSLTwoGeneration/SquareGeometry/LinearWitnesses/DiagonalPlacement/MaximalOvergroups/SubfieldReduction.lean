module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups.DicksonReduction

/-!
# Using the literal prime-subfield embedding

Dickson's marked PGL₂(p) representation is onto PGL₂(K): injectivity and
its exact order give surjectivity. Its conjugator therefore identifies the
actual inner intersection with the scalar-extension image. Relative
normality puts the conjugated whole overgroup in that image's normalizer.

If the normalizer is inner, the original whole overgroup is inner as well,
contradicting containment of an ambient Sylow two-subgroup. The normalizer
bound remains an explicit input, owned by the prime-subfield calculation.
This is a conditional reduction, not an exclusion based only on an abstract
subgroup isomorphism.

Source: Huppert II.8.27 and the auxiliary calculation for Aschbacher--Smith
E.1.14(6), printed p.214, citing Aschbacher (1982), Lemma 4.10.
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups

open Subgroup GorensteinWalter
open PrimeGeometry.Diagonal.MaximalOvergroups

variable {F : Type*} [Field F] [Finite F]

local instance finitePGL : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

omit [Finite F] in
private theorem dickson_toPGL_eq :
    Glauberman.Dickson.h826_pslToPGL (K := F) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL := by
  ext x
  rfl

/-- The concrete subfield branch is impossible if its ambient normalizer
is inner. The embedding and conjugator are those returned by Dickson. -/
public theorem no_subfield_case_of_normalizer_le_inner {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M)
    (hnormalizer : ∀ K : Subfield F, Nat.card K = p →
      normalizer ((Glauberman.Dickson.h826_pglMap K.subtype).range : Set (PGL2 F)) ≤
        innerRange F)
    (e : inner M ≃* PGL2 (GaloisField p 1))
    (w : Glauberman.Dickson.SubfieldConjugacyWitness p 1 (inner M)) : False := by
  classical
  have hF := oddPrimePower_of_square_card hpodd hFcard
  let : (innerRange F).Normal := normal_of_index_eq_two (pgl2_psl2Range_index_eq_two F hF)
  let : (innerIn M).Normal := innerIn_normal hF M
  have hKcard : Nat.card w.K = p := by simpa only [pow_one] using w.card_eq
  have hGcard : Nat.card (GaloisField p 1) = p := by
    simpa only [pow_one] using GaloisField.card p 1 (by decide)
  have hcard : Nat.card (inner M) = Nat.card (PGL2 w.K) := by
    rw [Nat.card_congr e.toEquiv, pgl2_card_formula, pgl2_card_formula, hKcard, hGcard]
  have hsurj : Function.Surjective w.phi :=
    ((Nat.bijective_iff_injective_and_card w.phi).mpr ⟨w.phi_injective, hcard⟩).2
  let C : Subgroup (PGL2 F) := (inner M).map Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hC : C = (innerIn M).map M.subtype := by
    simp only [C, innerIn, Subgroup.map_comap_eq, Subgroup.subgroupOf_map_subtype,
      innerRange, inf_comm]
  have hMC : M ≤ normalizer (C : Set (PGL2 F)) := by
    rw [hC]
    have h := Subgroup.le_normalizer_map (H := innerIn M) M.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, M.range_subtype] using h
  let c : MulAut (PGL2 F) := MulAut.conj w.conjugator
  have hc : C.map c.toMonoidHom = (Glauberman.Dickson.h826_pglMap w.K.subtype).range := by
    ext x
    constructor
    · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨w.phi ⟨h, hh⟩, ?_⟩
      have heq := w.map_phi ⟨h, hh⟩
      rw [dickson_toPGL_eq] at heq
      exact heq
    · rintro ⟨a, rfl⟩
      obtain ⟨h, rfl⟩ := hsurj a
      refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL h.val,
        ⟨h.val, h.property, rfl⟩, ?_⟩
      have heq := w.map_phi h
      rw [dickson_toPGL_eq] at heq
      exact heq.symm
  have hmapped : M.map c.toMonoidHom ≤ innerRange F := by
    apply (Subgroup.map_mono hMC).trans
    have hn := Subgroup.le_normalizer_map (H := C) c.toMonoidHom
    rw [hc] at hn
    exact hn.trans (hnormalizer w.K hKcard)
  have hML : M ≤ innerRange F := by
    intro m hm
    have hcm : c m ∈ innerRange F := hmapped ⟨m, hm, rfl⟩
    have hback := (inferInstance : (innerRange F).Normal).conj_mem
      (c m) hcm w.conjugator⁻¹
    simpa only [c, MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hback
  have hd := Subgroup.index_dvd_of_le (hTM.trans hML)
  change (innerRange F).index ∣ T.index at hd
  rw [show (innerRange F).index = 2 from pgl2_psl2Range_index_eq_two F hF] at hd
  exact T.not_dvd_index hd


end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups
