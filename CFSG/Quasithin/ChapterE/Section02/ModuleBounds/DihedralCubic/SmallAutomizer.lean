module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Strict
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The small automizer calculation in E.2.17

In a genuine two-conjugate dihedral configuration, an ambient faithful action
with automizer order at most four and cubic ratio greater than one forces
A/Z to have rank two and its fixed space to have codimension three. If V has
order sixteen, the actual factors A and B have order eight, their intersection
Z has order two, and P=BA has order thirty-two. Independently of these numerical
hypotheses, the two-conjugate geometry identifies C_P(V)=P∩V=B.

The proof excludes rank one using the elementary-core fixed-space bound,
then uses the exact action kernel A∩C(V)=Z and normalized product cardinality.
The companion SmallAutomizerAction applies this to the original ambient
quotient and proves that P covers its entire automizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.2.17, first paragraph, printed p.229. The input
|VJ/J|=2 retains the preceding dihedral reduction. No normalization of P by
an ambient overgroup or global normal-closure classification is asserted.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative ENNReal Pointwise
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X D Q : Type*} [Group X] [Finite X] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- The actual actor is a four-group with fixed codimension three. -/
theorem actor_rank_two_of_small_automizer
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (hD : Nat.card D ≤ 4) (hq : 1 < cubicRatio ρ) :
    rank f.range = 2 ∧ Nat.card f.range = 4 ∧
      IsElementaryAbelian 2 f.range ∧ fixedCodim ρ f.range = 3 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have hr : rank f.range ≤ 2 := by
    have hh := (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans hD
    rw [he.card_eq_two_pow_rank] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hn : rank f.range ≠ 1 := by
    intro hn
    have hi : (Z V g).relIndex (A V M g) = 2 := by
      change ((Z V g).subgroupOf (A V M g)).index = 2
      rw [← hk,index_ker,he.card_eq_two_pow_rank,hn]
      norm_num
    have hb := h.actor_fixed_bound_one_of_P_elementary hcard
      (h.P_elementary_of_actor_index_two hi) e ρ f ha
    have hle : cubicRatio ρ ≤ (1 : ℕ) := (cubicRatio_le_nat_iff ρ 1).mpr
      ⟨f.range,he,hc,by simpa only [one_mul,hn] using hb⟩
    exact (not_le_of_gt hq) (by simpa only [Nat.cast_one] using hle)
  have heq : rank f.range = 2 := by have := he.rank_pos; omega
  have hb := h.actor_fixed_bound_add_one hcard e ρ f hk he ha
  have hcod : fixedCodim ρ f.range = 3 := by
    by_contra hn
    have hle : cubicRatio ρ ≤ (1 : ℕ) := (cubicRatio_le_nat_iff ρ 1).mpr
      ⟨f.range,he,hc,by rw [one_mul]; omega⟩
    exact (not_le_of_gt hq) (by simpa only [Nat.cast_one] using hle)
  exact ⟨heq,by rw [he.card_eq_two_pow_rank,heq]; decide,he.2,hcod⟩

/-- The full two-core centralizer is already determined by the pair geometry. -/
theorem P_inf_centralizer_eq_B (h : Hypotheses T V M g) :
    P V M g ⊓ centralizer (V : Set X) = B V M := by
  let := h.elementary
  have hBC : B V M ≤ centralizer (V : Set X) := inf_le_right.trans V.le_centralizer
  apply le_antisymm
  · rintro x ⟨hxP, hxC⟩
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp
      (h.core_geometry.2.1 ▸ (show x ∈ (P V M g : Set X) from hxP))
    have haC : a ∈ centralizer (V : Set X) := by
      simpa only [inv_mul_cancel_left] using
        (centralizer (V : Set X)).mul_mem ((centralizer _).inv_mem (hBC hb)) hxC
    have haZ : a ∈ Z V g := h.A_inf_centralizer_eq_Z ▸ ⟨ha, haC⟩
    exact (B V M).mul_mem hb (h.Z_le_B_inf_A haZ).1
  · exact le_inf le_sup_left hBC

/-- The order calculation in the first paragraph of E.2.17. -/
theorem small_automizer_core_orders
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (hV : Nat.card V = 16)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (hD : Nat.card D ≤ 4) (hq : 1 < cubicRatio ρ) :
    Nat.card (A V M g) = 8 ∧ Nat.card (B V M) = 8 ∧
      Nat.card (Z V g) = 2 ∧ Nat.card (P V M g) = 32 ∧
      P V M g ⊓ centralizer (V : Set X) = P V M g ⊓ V := by
  have hk := h.actor_kernel e ρ hρ f ha
  have hr := h.actor_rank_two_of_small_automizer hproper hfit hcard e ρ hρ f ha hD hq
  have hVA := h.card_V_eq_twice_A hcard
  have hA : Nat.card (A V M g) = 8 := by omega
  have hABc : Nat.card (A V M g) = Nat.card (B V M) :=
    card_map_of_injective (MulAut.conj g).injective
  have hB : Nat.card (B V M) = 8 := by omega
  have hZA := f.ker.card_mul_index
  rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe
    (h.Z_le_B_inf_A.trans inf_le_right)).toEquiv, hr.2.1, hA] at hZA
  have hZ : Nat.card (Z V g) = 2 := by omega
  have hn : A V M g ≤ normalizer (B V M : Set X) :=
    le_normalizer_iff_commutator_le_right.mpr
      (h.commutator_A_B_le_Z.trans (h.Z_le_B_inf_A.trans inf_le_left))
  have hAB := card_mul_eq_card_inf_mul_card_sup_of_normalizes (B V M) (A V M g) hn
  rw [h.B_inf_A_eq_Z, hA, hB, hZ] at hAB
  refine ⟨hA, hB, hZ, ?_, ?_⟩
  · change Nat.card (B V M ⊔ A V M g : Subgroup X) = 32
    omega
  · rw [h.P_inf_V_eq_B, h.P_inf_centralizer_eq_B]

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
