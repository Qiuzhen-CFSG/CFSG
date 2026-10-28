module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.RadicalAction.RootCurve
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.PositiveTwoGroup
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.TorusScaling
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# The Suzuki-side root radical is a self-centralizing two-group

The radical lies in the positive matrix subgroup, whose height grading proves
it is a two-group. For self-centralization, let a surjection from the fixed
seed onto the actual Suzuki matrix group have this radical as its kernel.
Simplicity makes the image of the radical centralizer trivial or surjective.
In the latter case every seed element acts on the radical by an inner
automorphism of the radical, hence with power-of-two order.

A concrete middle-node torus word scales the fixed end-root curve by a
nonidentity scalar. The curve is injective by a single matrix entry. Iterating
an inner action of power-of-two order would make that scalar a power-of-two
root of unity in characteristic two, a contradiction. Thus the centralizer
lies in the radical. This uses no Ree simplicity or radical order formula.

The two-group conclusion is unconditional. The centralizer theorem takes only
the concrete quotient map, surjectivity and exact kernel identity as additional
premises, as permitted for the separate Suzuki quotient construction. Normality
and centralization are relative to the fixed seed. The parent `SuzukiCore`
assembly must supply that projection before claiming the full local result.

Source: the local radical in Aschbacher–Smith F.1.12(I)(5), printed p.263,
and the local characteristic-two use in 2.3.9(7), printed p.526 of
`refs/quasithin.pdf`.
-/

public section

namespace ReeF4.LargeLocalSeeds

open Subgroup Parabolics.OuterLocal.SuzukiCommutators

private theorem centralizer_le_kernel_of_scalar_action
    {G H F : Type*} [Group G] [Group H] [IsSimpleGroup H] [Field F] [CharP F 2]
    (f : G →* H) (hf : Function.Surjective f) (hP : IsPGroup 2 f.ker)
    (x : F → G) (hx : Function.Injective x) (hxR : ∀ t, x t ∈ f.ker)
    (g : G) (a : F) (ha : a ≠ 1)
    (hscale : ∀ t, g * x t * g⁻¹ = x (a * t)) :
    centralizer (f.ker : Set G) ≤ f.ker := by
  let C : Subgroup G := centralizer (f.ker : Set G)
  have hn : (C.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases hn.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff C).mp h
  · have hgen : C ⊔ f.ker = ⊤ := by
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top] using
        congrArg (Subgroup.comap f) h
    obtain ⟨c, hc, r, hr, hcr⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hgen ▸ (Subgroup.mem_top g))
    have hrc : Commute r c := Subgroup.mem_centralizer_iff.mp hc r hr
    have hcx (t : F) : c * x t * c⁻¹ = x t :=
      mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hc (x t) (hxR t)).symm
    have hrs (t : F) : r * x t * r⁻¹ = x (a * t) := by
      rw [← hscale, ← hcr, ← hrc.eq]
      calc
        r * x t * r⁻¹ = r * (c * x t * c⁻¹) * r⁻¹ := by rw [hcx]
        _ = (r * c) * x t * (r * c)⁻¹ := by group
    have hrsp (k : ℕ) (t : F) : r ^ k * x t * (r ^ k)⁻¹ = x (a ^ k * t) := by
      induction k with
      | zero => simp
      | succ k ih =>
        calc
          _ = r * (r ^ k * x t * (r ^ k)⁻¹) * r⁻¹ := by rw [pow_succ']; group
          _ = x (a * (a ^ k * t)) := by rw [ih, hrs]
          _ = _ := by rw [pow_succ', mul_assoc]
    obtain ⟨n, hn⟩ := hP ⟨r, hr⟩
    have hrpow : r ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have he : a ^ (2 ^ n) = 1 := by
      apply hx
      simpa only [hrpow, one_mul, inv_one, mul_one] using (hrsp (2 ^ n) 1).symm
    exact (ha (iterateFrobenius_inj F 2 n (by simpa only [iterateFrobenius_def, one_pow] using he))).elim

/-- The root-defined Suzuki radical inherits the two-group property from the
positive matrix subgroup, for every coefficient field in the Ree construction. -/
theorem suzuki_seedRadical_isPGroup {m : ℕ} (d : LocalBlockInput m) :
    IsPGroup 2 (seedRadical d .suzuki) :=
  ((standardUnipotent_isPGroup d).to_le
    (standardRadical_le_unipotent d .suzuki)).comap_subtype

/-- For the simple Suzuki range, a surjective Suzuki projection with the exact
root radical as kernel makes that radical self-centralizing inside the seed.
The nontrivial torus action used in the proof is calculated on the actual
root matrices; no action or centralizer conclusion is an input. -/
theorem suzuki_seedRadical_centralizer_le_of_projection {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m)
    (π : standardSeed d .suzuki →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki) :
    centralizer (seedRadical d .suzuki : Set (standardSeed d .suzuki)) ≤
      seedRadical d .suzuki := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  have hcard : 2 < Nat.card (CoefficientField m) := by
    rw [field_card]
    have h := Nat.pow_lt_pow_right (a := 2) (by omega) (show 1 < 2 * m + 1 by omega)
    simpa using h
  have : Nontrivial (CoefficientField m)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]
    omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : (CoefficientField m)ˣ)
  have hscalar : ((u : CoefficientField m) ^ 2)⁻¹ ≠ 1 := by
    intro hc
    apply hu
    apply Units.ext
    have hs : (u : CoefficientField m) ^ 2 = 1 := inv_eq_one.mp hc
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq, Units.val_one] using h
  have hP : IsPGroup 2 π.ker := hker ▸ suzuki_seedRadical_isPGroup d
  have hc := centralizer_le_kernel_of_scalar_action π hπ hP
    (endRootElement d) (SuzukiRadicalAction.endRootElement_injective d)
    (fun t => hker ▸ endRootElement_mem_radical d t)
    (middleTorusElement d u) (((u : CoefficientField m) ^ 2)⁻¹) hscalar
    (middleTorusElement_scaling d u)
  simpa only [hker] using hc

end ReeF4.LargeLocalSeeds
