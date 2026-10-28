module

public import Theory.GroupAction.IrreducibleTwoCoreKernel

/-!
# Irreducibility from a generating fixed line

Let a group act on a finite elementary abelian two-group. If a two-subgroup
of the actors has precisely two common fixed points, and the orbit of that
fixed line generates the whole group, every nonzero invariant subgroup is
all of the group. Orbit counting supplies a nonidentity fixed point in the
subgroup, and the unique fixed line then generates everything.

This is the argument in Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), Lemma 15.3.57(1), printed p.1148.
The source applies it to the genuine action of `H` on `U/Z`, with the image
of `Z_S` as the fixed line. Faithfulness and a Sylow hypothesis are not
needed for this particular argument.
-/

open Subgroup

/-- A nontrivial invariant subgroup contains the generating fixed line. -/
public theorem invariant_eq_top_of_fixed_line_generates
    {G W : Type*} [Group G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (T : Subgroup G) (hT : IsPGroup 2 T)
    (hfixed : Nat.card (FixedPoints.subgroup T W) = 2)
    (hgen : closure {w : W | ∃ g : G, ∃ z ∈ FixedPoints.subgroup T W, g • z = w} = ⊤)
    (D : Subgroup W) (hD : ∀ g : G, ∀ w ∈ D, g • w ∈ D) (hne : D ≠ ⊥) :
    D = ⊤ := by
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
  obtain ⟨d, hd⟩ := ne_bot_iff_exists_ne_one.mp (irreducible_fixed_nontrivial (W := D) T hT)
  have hdW : (d : D).val ≠ 1 := fun hh => hd (Subtype.ext (Subtype.ext hh))
  have hdFix : (d : D).val ∈ FixedPoints.subgroup T W := by
    intro t
    exact congrArg Subtype.val (d.property t)
  have htwo : ∀ w ∈ FixedPoints.subgroup T W, w = 1 ∨ w = (d : D).val := by
    intro w hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · have huniq := (Nat.card_eq_two_iff' (1 : FixedPoints.subgroup T W)).mp hfixed
      exact Or.inr (congrArg Subtype.val (huniq.unique
        (show (⟨w, hw⟩ : FixedPoints.subgroup T W) ≠ 1 from
          fun hh => hw1 (congrArg Subtype.val hh))
        (show (⟨(d : D).val, hdFix⟩ : FixedPoints.subgroup T W) ≠ 1 from
          fun hh => hdW (congrArg Subtype.val hh))))
  apply top_unique
  rw [← hgen]
  apply (closure_le _).mpr
  rintro w ⟨g, z, hz, rfl⟩
  rcases htwo z hz with rfl | rfl
  · exact hD g 1 D.one_mem
  · exact hD g _ (d : D).property

/-- A generating fixed line for a two-subgroup forces irreducibility. -/
public theorem irreducible_of_fixed_line_generates
    {G W : Type*} [Group G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (T : Subgroup G) (hT : IsPGroup 2 T)
    (hfixed : Nat.card (FixedPoints.subgroup T W) = 2)
    (hgen : closure {w : W | ∃ g : G, ∃ z ∈ FixedPoints.subgroup T W, g • z = w} = ⊤)
    (D : Subgroup W) (hD : ∀ g : G, ∀ w ∈ D, g • w ∈ D) :
    D = ⊥ ∨ D = ⊤ := by
  by_cases h : D = ⊥
  · exact Or.inl h
  · exact Or.inr (invariant_eq_top_of_fixed_line_generates T hT hfixed hgen D hD h)
