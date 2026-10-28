module

public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.Geometry
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.OddDihedral.Recognition

/-!
# The odd dihedral branch of E.2.10

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.2.10(6), printed pp. 222–223.

The equality `P ∩ V = J ∩ V` transfers the order-two hypothesis to `X/P`.
Its two conjugate involution generators give an odd dihedral model, and its
center lies in the image of `V`. Clause (4), supplied as the explicit premise
`hcentral`, puts the image of `J` in that center. Since `J ∩ V = B ≤ P`, this
image is trivial. The inclusions `P ≤ O₂(X) ≤ J` now give all three equalities,
and transport gives the same dihedral model for `X/J`.

The preceding central-action clause is intentionally an assembly input; no
additional order or model hypothesis is used in the recognition.
-/

@[expose] public section

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- The images of `V` in `X/P` and `X/J` have the same order, since their
kernels are both `B`. -/
theorem quotient_P_card_two (h : Hypotheses T V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    letI := h.core_geometry.1
    Nat.card (V.map (QuotientGroup.mk' (P V M g))) = 2 := by
  let := h.core_geometry.1
  calc
    Nat.card (V.map (QuotientGroup.mk' (P V M g))) = (P V M g).relIndex V := by
      rw [← relIndex_ker, QuotientGroup.ker_mk']
    _ = (B V M).relIndex V := by
      rw [← inf_relIndex_right, h.P_inf_V_eq_B]
    _ = (J M).relIndex V := inf_relIndex_right _ _
    _ = 2 := by rw [← QuotientGroup.ker_mk' (J M), relIndex_ker]; exact hcard

/-- Recognition from the two conjugate involution generators of `X/P`,
including the center containment used to eliminate `J/P`. -/
theorem quotient_P_recognition (h : Hypotheses T V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    letI := h.core_geometry.1
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ Nonempty ((X ⧸ P V M g) ≃* DihedralGroup m) ∧
      center (X ⧸ P V M g) ≤ V.map (QuotientGroup.mk' (P V M g)) := by
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (P V M g)
  obtain ⟨v, hv1, hvuniq⟩ := (Nat.card_eq_two_iff' (1 : V.map q)).mp
    (h.quotient_P_card_two hcard)
  have hvne : (v : X ⧸ P V M g) ≠ 1 := by
    intro hh
    exact hv1 (Subtype.ext hh)
  have hv2 : (v : X ⧸ P V M g) ^ 2 = 1 := by
    let := h.elementary
    let := IsElementaryAbelian.map (p := 2) (A := V) q
    exact elemPow_eq_one_of_isElementaryAbelian (A := V.map q) v v.property
  have hvgen : V.map q = zpowers (v : X ⧸ P V M g) := by
    apply le_antisymm
    · intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact one_mem _
      · have he : (⟨x,hx⟩ : V.map q) = v := hvuniq _ (fun he => hx1 (congrArg Subtype.val he))
        rw [show x = (v : X ⧸ P V M g) from congrArg Subtype.val he]
        exact mem_zpowers _
    · exact zpowers_le.mpr v.property
  let b := (MulAut.conj (q g)) (v : X ⧸ P V M g)
  have hb2 : b ^ 2 = 1 := by
    change ((MulAut.conj (q g)) (v : X ⧸ P V M g)) ^ 2 = 1
    rw [← map_pow, hv2, map_one]
  have hw : (W V g).map q = zpowers b := by
    have hm : (W V g).map q = (V.map q).map (MulAut.conj (q g)).toMonoidHom := by
      rw [W, map_map, map_map]
      congr 1
    rw [hm, hvgen, MonoidHom.map_zpowers]
    rfl
  have hg : zpowers (v : X ⧸ P V M g) ⊔ zpowers b = ⊤ := by
    rw [← hvgen, ← hw, ← Subgroup.map_sup, h.generate]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hc : IsConj (v : X ⧸ P V M g) b := isConj_iff.mpr ⟨q g, rfl⟩
  obtain ⟨m, hm, ho, he, hz⟩ := OddDihedral.recognition hvne hv2 hb2 hg hc
  exact ⟨m, hm, ho, he, hvgen.symm ▸ hz⟩

/-- E.2.10(6), with the preceding clause (4) supplied explicitly. The two
quotients are identified with the same actual odd dihedral group. -/
theorem odd_dihedral_of_card_two (h : Hypotheses T V M g)
    (hcentral : ⁅J M, (⊤ : Subgroup X)⁆ ≤ P V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    letI := h.core_geometry.1
    P V M g = pCore 2 X ∧ pCore 2 X = J M ∧
      ∃ m : ℕ, 0 < m ∧ Odd m ∧
        Nonempty ((X ⧸ P V M g) ≃* DihedralGroup m) ∧
        Nonempty ((X ⧸ J M) ≃* DihedralGroup m) := by
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (P V M g)
  obtain ⟨m, hm, ho, ⟨e⟩, hz⟩ := h.quotient_P_recognition hcard
  have hJC : (J M).map q ≤ center (X ⧸ P V M g) := by
    rw [← centralizer_univ, ← coe_top, ← commutator_eq_bot_iff_le_centralizer]
    rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective _), ← map_commutator]
    apply bot_unique
    exact (map_mono hcentral).trans (by simp [q])
  have hJP : J M ≤ P V M g := by
    intro j hj
    have hjV := hz (hJC (mem_map_of_mem q hj))
    obtain ⟨v, hv, he⟩ := mem_map.mp hjV
    have hjv : j * v⁻¹ ∈ P V M g := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (j * v⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hvJ : v ∈ J M := by
      have hh := (J M).mul_mem ((J M).inv_mem (h.P_le_J hjv)) hj
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
    apply (QuotientGroup.eq_one_iff _).mp
    change q j = 1
    rw [← he]
    exact (QuotientGroup.eq_one_iff _).mpr
      ((le_sup_left : B V M ≤ P V M g) ⟨hvJ, hv⟩)
  have hPJ : P V M g = J M := le_antisymm h.P_le_J hJP
  have hPQ : P V M g = pCore 2 X :=
    le_antisymm h.P_le_twoCore (h.twoCore_le_J.trans hJP)
  exact ⟨hPQ, hPQ.symm.trans hPJ, m, hm, ho, ⟨e⟩,
    ⟨(QuotientGroup.quotientMulEquivOfEq hPJ.symm).trans e⟩⟩
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
