module

public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Indecomposability from a fixed line

A two-group has a nonidentity fixed point on every nontrivial finite binary
module. If its fixed subgroup has order two, every nontrivial invariant
subgroup contains that same line. Thus two invariant subgroups with trivial
intersection cannot both be nontrivial. The final theorem applies this to
actual conjugation on a normal elementary abelian subgroup.

This is the fixed-point argument used for the E₁₆ branch of
Aschbacher--Smith, Lemma 14.2.21, printed p.988.
-/

open Subgroup

/-- Every nontrivial invariant subgroup contains the unique fixed line. -/
public theorem invariant_contains_fixed_line
    {G W : Type*} [Group G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (T : Subgroup G) (hT : IsPGroup 2 T)
    (hfixed : Nat.card (FixedPoints.subgroup T W) = 2)
    (D : Subgroup W) (hD : ∀ g : G, ∀ w ∈ D, g • w ∈ D) (hne : D ≠ ⊥) :
    FixedPoints.subgroup T W ≤ D := by
  classical
  let : IsInvariant G W D := ⟨fun g w => ⟨hD g w, fun hw => by
    simpa only [inv_smul_smul] using hD g⁻¹ (g • w) hw⟩⟩
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hne
  let : IsElementaryAbelian 2 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) w.val) }
  obtain ⟨d, hd⟩ := ne_bot_iff_exists_ne_one.mp
    (irreducible_fixed_nontrivial (W := D) T hT)
  have hdW : (d : D).val ≠ 1 := fun hh => hd (Subtype.ext (Subtype.ext hh))
  have hdFix : (d : D).val ∈ FixedPoints.subgroup T W := by
    intro t
    exact congrArg Subtype.val (d.property t)
  intro w hw
  by_cases hw1 : w = 1
  · exact hw1 ▸ D.one_mem
  · have huniq := (Nat.card_eq_two_iff' (1 : FixedPoints.subgroup T W)).mp hfixed
    have he : w = (d : D).val := congrArg Subtype.val (huniq.unique
      (show (⟨w, hw⟩ : FixedPoints.subgroup T W) ≠ 1 from
        fun hh => hw1 (congrArg Subtype.val hh))
      (show (⟨(d : D).val, hdFix⟩ : FixedPoints.subgroup T W) ≠ 1 from
        fun hh => hdW (congrArg Subtype.val hh)))
    exact he ▸ (d : D).property

/-- A fixed line for a two-subgroup obstructs invariant direct decompositions. -/
public theorem invariant_disjoint_of_fixed_line
    {G W : Type*} [Group G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (T : Subgroup G) (hT : IsPGroup 2 T)
    (hfixed : Nat.card (FixedPoints.subgroup T W) = 2)
    (U V : Subgroup W)
    (hU : ∀ g : G, ∀ w ∈ U, g • w ∈ U)
    (hV : ∀ g : G, ∀ w ∈ V, g • w ∈ V)
    (hd : Disjoint U V) : U = ⊥ ∨ V = ⊥ := by
  by_cases hu : U = ⊥
  · exact Or.inl hu
  by_cases hv : V = ⊥
  · exact Or.inr hv
  have hu' := invariant_contains_fixed_line T hT hfixed U hU hu
  have hv' := invariant_contains_fixed_line T hT hfixed V hV hv
  have hf : FixedPoints.subgroup T W = ⊥ :=
    le_bot_iff.mp ((le_inf hu' hv').trans (disjoint_iff.mp hd).le)
  have hc := Subgroup.card_bot (G := W)
  rw [hf, hc] at hfixed
  omega

/-- The fixed-line obstruction for literal conjugation in the ambient group. -/
public theorem Subgroup.disjoint_invariant_of_centralizer_card_two
    {D : Type*} [Group D] [Finite D]
    (Q QK Z : Subgroup D) [Q.Normal] [IsElementaryAbelian 2 Q]
    (hQK : IsPGroup 2 QK)
    (hZ : Nat.card Z = 2)
    (hcentral : Q ⊓ centralizer (QK : Set D) = Z)
    (U V : Subgroup Q)
    (hU : ∀ g : D, ∀ u ∈ U, MulAut.conjNormal g u ∈ U)
    (hV : ∀ g : D, ∀ v ∈ V, MulAut.conjNormal g v ∈ V)
    (hd : Disjoint U V) : U = ⊥ ∨ V = ⊥ := by
  have hmap : (FixedPoints.subgroup (⊤ : Subgroup QK) Q).map Q.subtype = Z := by
    rw [← hcentral]
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.property, ?_⟩
      intro k hk
      have hh := congrArg Q.subtype (hq ⟨⟨k, hk⟩, mem_top _⟩)
      change k * (q : D) * k⁻¹ = q at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · rintro ⟨hxQ, hxC⟩
      refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
      intro k
      apply Subtype.ext
      change ((k : QK) : D) * x * ((k : QK) : D)⁻¹ = x
      exact mul_inv_eq_iff_eq_mul.mpr (hxC k k.val.property)
  have hfixed : Nat.card (FixedPoints.subgroup (⊤ : Subgroup QK) Q) = 2 := by
    rw [← card_map_of_injective (K := FixedPoints.subgroup (⊤ : Subgroup QK) Q)
      Q.subtype_injective, hmap, hZ]
  exact invariant_disjoint_of_fixed_line (⊤ : Subgroup QK) (hQK.to_subgroup ⊤) hfixed
    U V (fun g u hu => hU g u hu) (fun g v hv => hV g v hv) hd
