module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Bounds
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Placement of same-orientation quadratic offenders in degree five

Quadraticity places the actor in the radical of its natural fixed space.
Transvections with centres in that space and a fixed hyperplane axis give
an axis factor. The product-order formula bounds the intersection with the
actor. If there is no internal axis four-group, the fixed space has dimension
three, the actor has rank four, and its intersection with the axis factor
has order two. All geometry is transported through the original marking.

Source: Aschbacher–Smith, B.4.9, final paragraph on printed p.95,
combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
open QuasisimpleSource BinaryLinear BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)

private noncomputable def radicalEquiv (W : Submodule (ZMod 2) (Space 5)) :
    markedRadical d hF W ≃* radical W where
  toFun a := ⟨groupEquiv d hF a, a.property⟩
  invFun a := ⟨(groupEquiv d hF).symm a, by
    change groupEquiv d hF ((groupEquiv d hF).symm a) ∈ radical W
    simpa only [MulEquiv.apply_symm_apply] using a.property⟩
  left_inv a := Subtype.ext ((groupEquiv d hF).symm_apply_apply a)
  right_inv a := Subtype.ext ((groupEquiv d hF).apply_symm_apply a)
  map_mul' a b := Subtype.ext ((groupEquiv d hF).map_mul a b)

private theorem radical_card_le (W : Submodule (ZMod 2) (Space 5)) :
    Nat.card (markedRadical d hF W) ≤
      2 ^ ((5 - Module.finrank (ZMod 2) W) * Module.finrank (ZMod 2) W) := by
  rw [Nat.card_congr (radicalEquiv d hF W).toEquiv]
  exact BinaryNaturalDual.FiveActors.Classification.card_radical_le W

private theorem radical_elementary (W : Submodule (ZMod 2) (Space 5)) :
    IsElementaryAbelian 2 (markedRadical d hF W) :=
  IsElementaryAbelian.of_surjective (radicalEquiv d hF W).symm.toMonoidHom
    (radicalEquiv d hF W).symm.surjective

private theorem hyperplane_factor (W : Submodule (ZMod 2) (Space 5))
    (hW : Module.finrank (ZMod 2) W < 5) :
    ∃ H : Submodule (ZMod 2) (Space 5), Module.finrank (ZMod 2) H = 4 ∧ W ≤ H ∧
      2 ^ Module.finrank (ZMod 2) W ≤
        Nat.card (markedRadical d hF W ⊓ markedRadical d hF H : Subgroup G) := by
  have hne : W ≠ ⊤ := by
    intro he
    have hd : Module.finrank (ZMod 2) W = 5 := by rw [he]; simp [Space]
    omega
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  obtain ⟨φ, hφx, hWφ⟩ := W.exists_le_ker_of_notMem hx
  have hφx1 : φ x = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hφx
  have hφ : φ ≠ 0 := by intro he; apply hφx; simp [he]
  have hH : Module.finrank (ZMod 2) φ.ker = 4 := by
    have he := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    have hd : Module.finrank (ZMod 2) (Space 5) = 5 := by simp [Space]
    omega
  let K := markedRadical d hF W ⊓ markedRadical d hF φ.ker
  let t : W → K := fun w =>
    ⟨(groupEquiv d hF).symm (transvection w φ (hWφ w.property)), by
      change groupEquiv d hF ((groupEquiv d hF).symm _) ∈ radical W ∧
        groupEquiv d hF ((groupEquiv d hF).symm _) ∈ radical φ.ker
      rw [MulEquiv.apply_symm_apply]
      exact ⟨transvection_mem w.property hWφ, transvection_mem (hWφ w.property) le_rfl⟩⟩
  have ht : Function.Injective t := by
    intro w z he
    have hh := congrArg (fun a : K => groupEquiv d hF a x) he
    change groupEquiv d hF ((groupEquiv d hF).symm _) x =
      groupEquiv d hF ((groupEquiv d hF).symm _) x at hh
    simp only [MulEquiv.apply_symm_apply] at hh
    change x + φ x • (w : Space 5) = x + φ x • (z : Space 5) at hh
    simp only [hφx1, one_smul, add_right_inj] at hh
    exact Subtype.ext hh
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  refine ⟨φ.ker, hH, hWφ, ?_⟩
  have hc := Nat.card_le_card_of_injective t ht
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact hc

private theorem card_product_bound [Finite G]
    {W : Submodule (ZMod 2) (Space 5)} {A C : Subgroup G}
    (hA : A ≤ markedRadical d hF W) (hC : C ≤ markedRadical d hF W) :
    Nat.card A * Nat.card C ≤ Nat.card (A ⊓ C : Subgroup G) *
      2 ^ ((5 - Module.finrank (ZMod 2) W) * Module.finrank (ZMod 2) W) := by
  have hn : C ≤ Subgroup.normalizer (A : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply (groupEquiv d hF).injective
    simp only [map_mul]
    exact radical_commute W (hA ha) (hC hc)
  rw [Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes A C hn]
  exact Nat.mul_le_mul_left _
    ((Subgroup.card_le_of_le (sup_le hA hC)).trans (radical_card_le d hF W))

private theorem rank_ge_two_of_card [Finite G] {A : Subgroup G}
    (hA : IsElementaryTwo A) (hc : 2 < Nat.card A) : 2 ≤ rank A := by
  by_contra hr
  have hh : 2 ^ rank A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [← hA.card_eq_two_pow_rank] at hh
  norm_num at hh
  omega

variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
include hF in
private theorem natural_dim : Module.finrank (ZMod 2) d.space.toSubmodule = 5 := by
  rw [(coordinates d hF).linearEquiv.finrank_eq]
  change Module.finrank (ZMod 2) (Space 5) = 5
  simp [Space]

private theorem cost_one_of_hyperplane
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {H : Submodule (ZMod 2) (Space 5)} (hH : Module.finrank (ZMod 2) H = 4)
    {A : Subgroup G} (hne : A ≠ ⊥) (hA : A ≤ markedRadical d hF H) :
    fixedCodim d.space.quotientRepresentation A = 1 := by
  let c : d.space.toSubmodule ≃ₗ[ZMod 2] Space 5 := (coordinates d hF).linearEquiv
  have hfix : H.map c.symm.toLinearMap ≤ fixedSpace d.space.toRepresentation A := by
    rintro _ ⟨x, hx, rfl⟩ a
    apply c.injective
    change c (d.space.toRepresentation a (c.symm x)) = c (c.symm x)
    have he : c (d.space.toRepresentation a (c.symm x)) =
        groupEquiv d hF a (c (c.symm x)) := intertwines d hF a (c.symm x)
    rw [he, c.apply_symm_apply]
    exact (hA a.property).1 x hx
  have hd : Module.finrank (ZMod 2) (H.map c.symm.toLinearMap) = 4 :=
    (c.symm.finrank_map_eq H).trans hH
  have hm := Submodule.finrank_mono hfix
  have hs := fixedCodim_add_finrank d.space.toRepresentation A
  have hp := fixedCodim_pos_of_faithful d.space.quotientRepresentation d.quotient_faithful hne
  rw [← factor_costs_eq d e, natural_dim d hF] at hs
  omega

private theorem hyperplane_intersection_card_le_two
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {B : Subgroup G} (hB : IsElementaryTwo B)
    (hno : ¬ ∃ E : Subgroup G, E ≤ B ∧ QuadraticSplitting.IsAxisFour d E)
    {H : Submodule (ZMod 2) (Space 5)} (hH : Module.finrank (ZMod 2) H = 4) :
    Nat.card (B ⊓ markedRadical d hF H : Subgroup G) ≤ 2 := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  by_contra hc
  have hcard : 2 < Nat.card (B ⊓ markedRadical d hF H : Subgroup G) := by omega
  have hne := (Subgroup.one_lt_card_iff_ne_bot _).mp (by omega :
    1 < Nat.card (B ⊓ markedRadical d hF H : Subgroup G))
  have hD := hB.of_le inf_le_left hne
  obtain ⟨E, hED, hE⟩ := axisFour_subgroup_of_cost_one d hF hD
    (rank_ge_two_of_card hD hcard)
    (cost_one_of_hyperplane d hF e hH hne inf_le_right)
  exact hno ⟨E, hED.trans inf_le_left, hE⟩

private theorem fixed_radical_position {B : Subgroup G} (hq : IsQuadratic ρ B) :
    ∃ W : Submodule (ZMod 2) (Space 5),
      Module.finrank (ZMod 2) W + fixedCodim d.space.toRepresentation B = 5 ∧
      B ≤ markedRadical d hF W := by
  let c : d.space.toSubmodule ≃ₗ[ZMod 2] Space 5 := (coordinates d hF).linearEquiv
  let W := (fixedSpace d.space.toRepresentation B).map c.toLinearMap
  refine ⟨W, ?_, ?_⟩
  · have hd := c.finrank_map_eq (fixedSpace d.space.toRepresentation B)
    have hs := fixedCodim_add_finrank d.space.toRepresentation B
    rw [natural_dim d hF] at hs
    change Module.finrank (ZMod 2) W = _ at hd
    omega
  · intro a ha
    constructor
    · rintro _ ⟨v, hv, rfl⟩
      exact (intertwines d hF a v).symm.trans (congrArg c (hv ⟨a, ha⟩))
    · intro x
      let v := c.symm x
      refine ⟨d.space.toRepresentation a v - v, ?_, ?_⟩
      · intro b
        apply Subtype.ext
        exact hq b b.property a ha v
      · change c (d.space.toRepresentation a v - v) = groupEquiv d hF a x - x
        rw [map_sub]
        have he : c (d.space.toRepresentation a v) = groupEquiv d hF a (c v) :=
          intertwines d hF a v
        rw [he]
        simp only [v, c.apply_symm_apply]

/-- The geometric alternative for every quadratic same-orientation offender.
The rank-six and rank-five cases force an actual internal axis four-group. -/
theorem placement_of_quadratic_offender
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {B : Subgroup G} (hB : IsOffender ρ B) (hq : IsQuadratic ρ B) :
    PlacementAlternative d hF B := by
  classical
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  by_cases haxis : ∃ E : Subgroup G, E ≤ B ∧ QuadraticSplitting.IsAxisFour d E
  · exact Or.inl haxis
  obtain ⟨hmin, _, hcostmin, hcostmax⟩ := bounds_of_no_axisFour d hF e hB haxis
  obtain ⟨W, hdim, hBR⟩ := fixed_radical_position d hF hq
  rw [← factor_costs_eq d e] at hdim
  have hWcases : Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3 := by
    omega
  obtain ⟨H, hH, hWH, hKcard⟩ := hyperplane_factor d hF W (by omega)
  let K := markedRadical d hF W ⊓ markedRadical d hF H
  have hI : B ⊓ K = B ⊓ markedRadical d hF H := by
    ext a
    constructor
    · exact fun ha => ⟨ha.1, ha.2.2⟩
    · exact fun ha => ⟨ha.1, hBR ha.1, ha.2⟩
  have hsmall := hyperplane_intersection_card_le_two d hF e hB.1 haxis hH
  have hprod := card_product_bound d hF hBR (show K ≤ markedRadical d hF W from inf_le_left)
  rw [hI, hB.1.card_eq_two_pow_rank] at hprod
  have hp : 2 ^ rank B * 2 ^ Module.finrank (ZMod 2) W ≤
      2 * 2 ^ ((5 - Module.finrank (ZMod 2) W) * Module.finrank (ZMod 2) W) :=
    (Nat.mul_le_mul_left _ hKcard).trans (hprod.trans (Nat.mul_le_mul_right _ hsmall))
  have hW : Module.finrank (ZMod 2) W = 3 := by
    rcases hWcases with hW | hW
    · have hbudget := twice_factor_cost_le_rank d e hB
      have hr6 : 6 ≤ rank B := by omega
      have hlarge : 2 ^ 6 ≤ 2 ^ rank B := Nat.pow_le_pow_right (by decide) hr6
      norm_num [hW] at hp
      norm_num at hlarge
      omega
    · exact hW
  have hr : rank B = 4 := by
    have hp' : 2 ^ rank B ≤ 2 ^ 4 := by norm_num [hW] at hp ⊢; omega
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp'
    omega
  have hcard : Nat.card (B ⊓ markedRadical d hF H : Subgroup G) = 2 := by
    have hK : 8 ≤ Nat.card K := by simpa only [hW, Nat.reducePow] using hKcard
    rw [hr, hW] at hprod
    norm_num only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at hprod
    omega
  have hKlarge : 2 < Nat.card K := by
    have : 8 ≤ Nat.card K := by simpa only [hW, Nat.reducePow] using hKcard
    omega
  have hKne : K ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).mp (by omega)
  have hRne : markedRadical d hF W ≠ ⊥ := by
    intro hh
    apply hKne
    exact le_bot_iff.mp (hh ▸ (show K ≤ markedRadical d hF W from inf_le_left))
  have hKel : IsElementaryTwo K :=
    (show IsElementaryTwo (markedRadical d hF W) from
      ⟨hRne, radical_elementary d hF W⟩).of_le inf_le_left hKne
  obtain ⟨E, hEK, hE⟩ := axisFour_subgroup_of_cost_one d hF hKel
    (rank_ge_two_of_card hKel hKlarge)
    (cost_one_of_hyperplane d hF e hH hKne inf_le_right)
  exact Or.inr ⟨W, H, ⟨hW, hH, hWH, hBR, hr, hcard⟩, E, hEK.trans inf_le_left, hE⟩

/-- Placement in the exact Sylow/minimal-offender contract used by B.4.9.
Minimality and Sylow containment are retained for the source consumer. -/
theorem placement
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    (T : Sylow 2 G) {B : Subgroup G} (_hBT : B ≤ (T : Subgroup G))
    (hB : IsMinimalBestOffender ρ B) (hq : IsQuadratic ρ B) :
    PlacementAlternative d hF B :=
  placement_of_quadratic_offender d hF e (hB.1.isOffender ρ) hq

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
