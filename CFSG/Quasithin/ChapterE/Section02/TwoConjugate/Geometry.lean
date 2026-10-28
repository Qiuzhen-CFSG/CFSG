module

public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.Setup
public import Theory.ElementaryAbelian.Join

/-!
# The two-conjugate quotient geometry

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.2.10(2), printed pp. 222–223.

The elementary abelian factors commute modulo their intersection, so their
images form an internal direct sum in `X/Z`. To determine the fixed points,
the preimage in `A` of its fixed subgroup is normalized by both generators.
Normality and conjugacy then put it in `V ∩ V^g = Z`. Factorization `P = BA`
therefore gives exactly `B/Z` as the fixed subgroup. Quadratic action is
inherited from the stronger unquotiented identity in `Setup`.
-/

@[expose] public section

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem Z_le_B_inf_A (h : Hypotheses T V M g) : Z V g ≤ B V M ⊓ A V M g := by
  let := h.elementary
  have hc := abelian_generator_intersection_le_pCore 2 V (W V g)
    (IsElementaryAbelian.isPGroup 2 V) h.generate
  rw [h.B_eq_twoCore_inf, h.A_eq_twoCore_inf]
  exact fun _ hz => ⟨⟨hc hz, hz.1⟩, ⟨hc hz, hz.2⟩⟩

theorem B_inf_A_eq_Z (h : Hypotheses T V M g) : B V M ⊓ A V M g = Z V g := by
  refine le_antisymm ?_ h.Z_le_B_inf_A
  rw [h.A_eq_twoCore_inf]
  exact fun _ hx => ⟨hx.1.2, hx.2.2⟩

theorem Z_normal (h : Hypotheses T V M g) : (Z V g).Normal := by
  have hc := h.core_geometry.2.2.trans inf_le_right
  exact ⟨fun z hz x => by rw [(mem_center_iff.mp (hc hz)) x, mul_inv_cancel_right]; exact hz⟩

omit [Finite X] in
theorem B_elementary (h : Hypotheses T V M g) : IsElementaryAbelian 2 (B V M) := by
  let := h.elementary
  exact {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      ((mem_centralizer_iff.mp (V.le_centralizer x.property.2)) y y.property.2).symm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := V) x x.property.2) }

omit [Finite X] in
theorem A_elementary (h : Hypotheses T V M g) : IsElementaryAbelian 2 (A V M g) := by
  let := h.B_elementary
  exact IsElementaryAbelian.map _

/-- The internal direct sum in E.2.10(2), stated as generation, trivial
intersection, and elementary abelianness of the actual images in `X/Z`. -/
theorem quotient_direct_sum (h : Hypotheses T V M g) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    IsElementaryAbelian 2 ((P V M g).map q) ∧
      (B V M).map q ⊔ (A V M g).map q = (P V M g).map q ∧
      (B V M).map q ⊓ (A V M g).map q = ⊥ := by
  let := h.Z_normal
  let q := QuotientGroup.mk' (Z V g)
  let := h.B_elementary
  let := h.A_elementary
  let := IsElementaryAbelian.map (p := 2) (A := B V M) q
  let := IsElementaryAbelian.map (p := 2) (A := A V M g) q
  have hc : ⁅(A V M g).map q, (B V M).map q⁆ = ⊥ := by
    rw [← map_commutator]
    apply bot_unique
    exact (map_mono h.commutator_A_B_le_Z).trans (by simp [q])
  refine ⟨?_, (Subgroup.map_sup _ _ _).symm, ?_⟩
  · change IsElementaryAbelian 2 ((B V M ⊔ A V M g).map q)
    rw [Subgroup.map_sup]
    exact IsElementaryAbelian.sup_of_le_centralizer
      (commutator_eq_bot_iff_le_centralizer.mp hc)
  · apply comap_injective (QuotientGroup.mk'_surjective (Z V g))
    rw [comap_inf, comap_map_eq, comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr (h.Z_le_B_inf_A.trans inf_le_left),
      sup_eq_left.mpr (h.Z_le_B_inf_A.trans inf_le_right), h.B_inf_A_eq_Z, MonoidHom.comap_bot]
    exact (QuotientGroup.ker_mk' _).symm

/-- The `A/Z` summand has no nontrivial fixed points under `V`. -/
theorem quotient_A_fixed_eq_bot (h : Hypotheses T V M g) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    (A V M g).map q ⊓ centralizer ((V.map q : Subgroup (X ⧸ Z V g)) : Set _) = ⊥ := by
  let := h.Z_normal
  let := h.elementary
  let q := QuotientGroup.mk' (Z V g)
  let D := A V M g ⊓ (centralizer (V.map q : Set (X ⧸ Z V g))).comap q
  have hZD : Z V g ≤ D := by
    intro z hz
    exact ⟨(h.Z_le_B_inf_A hz).2, by
      change q z ∈ centralizer _
      rw [show q z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
      exact one_mem _⟩
  have hDV : ⁅D, V⁆ ≤ Z V g := by
    apply commutator_le.mpr
    intro d hd v hv
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅d,v⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.mp hd.2 (q v) (mem_map_of_mem q hv)).symm
  have hDW : D ≤ W V g := by
    exact inf_le_left.trans (by rw [h.A_eq_twoCore_inf]; exact inf_le_right)
  have hDnormal : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← h.generate]
    exact sup_le (le_normalizer_iff_commutator_le_left.mpr (hDV.trans hZD))
      (((W V g).le_centralizer.trans (centralizer_le hDW)).trans
        (centralizer_le_normalizer _))
  have hD_le_V : D ≤ V := by
    intro d hd
    have hm := hDW (hDnormal.conj_mem d hd g)
    obtain ⟨v, hv, he⟩ := mem_map.mp hm
    have he' : (MulAut.conj g) v = (MulAut.conj g) d := he
    exact (MulAut.conj g).injective he' ▸ hv
  apply bot_unique
  rintro x ⟨hxA, hxC⟩
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hxA
  have haD : a ∈ D := ⟨ha, hxC⟩
  exact (QuotientGroup.eq_one_iff a).mpr ⟨hD_le_V haD, hDW haD⟩

/-- The exact fixed-point assertion in E.2.10(2). -/
theorem quotient_fixed_eq_B (h : Hypotheses T V M g) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    (P V M g).map q ⊓ centralizer ((V.map q : Subgroup (X ⧸ Z V g)) : Set _) =
      (B V M).map q := by
  let := h.Z_normal
  let := h.elementary
  let q := QuotientGroup.mk' (Z V g)
  have hBC : (B V M).map q ≤ centralizer (V.map q : Set (X ⧸ Z V g)) := by
    have hc : ⁅B V M, V⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (inf_le_right.trans V.le_centralizer)
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, hc, Subgroup.map_bot]
  apply le_antisymm
  · rintro x ⟨hxP, hxC⟩
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hxP
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp (h.core_geometry.2.1 ▸ (show p ∈ (P V M g : Set X) from hp))
    change q (b * a) ∈ centralizer (V.map q : Set (X ⧸ Z V g)) at hxC
    change q (b * a) ∈ (B V M).map q
    have hbq : q b ∈ (B V M).map q := mem_map_of_mem q hb
    have haq : q a ∈ (A V M g).map q := mem_map_of_mem q ha
    have hac : q a ∈ centralizer (V.map q : Set (X ⧸ Z V g)) := by
      have hh := (centralizer (V.map q : Set (X ⧸ Z V g))).mul_mem
        ((centralizer _).inv_mem (hBC hbq)) hxC
      simpa only [map_mul, inv_mul_cancel_left] using hh
    have ha1 : q a = 1 := by
      have hh : q a ∈ (A V M g).map q ⊓ centralizer (V.map q : Set (X ⧸ Z V g)) := ⟨haq, hac⟩
      rw [h.quotient_A_fixed_eq_bot] at hh
      exact hh
    rw [map_mul, ha1, mul_one]
    exact hbq
  · exact le_inf (map_mono le_sup_left) hBC
/-- Quadratic action on the quotient itself, as in E.2.10(2). -/
theorem quotient_quadratic (h : Hypotheses T V M g) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    ⁅⁅(P V M g).map q, V.map q⁆, V.map q⁆ = ⊥ := by
  let := h.Z_normal
  dsimp only
  rw [← map_commutator, ← map_commutator, h.quadratic, Subgroup.map_bot]

/-- The corresponding unquotiented fixed subgroup, used in E.2.13. -/
theorem A_inf_centralizer_eq_Z (h : Hypotheses T V M g) :
    A V M g ⊓ centralizer (V : Set X) = Z V g := by
  let := h.Z_normal
  let q := QuotientGroup.mk' (Z V g)
  apply le_antisymm
  · intro a ha
    have hc : q a ∈ centralizer (V.map q : Set (X ⧸ Z V g)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      simpa only [map_mul] using congrArg q (mem_centralizer_iff.mp ha.2 v hv)
    have hm : q a ∈ (A V M g).map q ⊓ centralizer (V.map q : Set (X ⧸ Z V g)) :=
      ⟨mem_map_of_mem q ha.1, hc⟩
    rw [h.quotient_A_fixed_eq_bot] at hm
    exact (QuotientGroup.eq_one_iff a).mp hm
  · exact le_inf (h.Z_le_B_inf_A.trans inf_le_right)
      ((h.core_geometry.2.2.trans inf_le_right).trans (center_le_centralizer _))
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
