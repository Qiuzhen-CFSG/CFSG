module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus

/-!
# Borel-invariant subgroups of the central symplectic root plane

The diagonal weights on the two central roots are a² and ab. Over a finite
field of characteristic two the square map is bijective, so these weights
provide independent nonzero scalings. When the field has more than two
elements, subtracting a scalar translate separates the two coordinates.
Thus the invariant subgroups are precisely the trivial subgroup, either
full root, and their product. The same weights show that the torus has no
nonidentity fixed element in this plane.

All subgroups use the actual matrix parametrization of the Sylow center.
These are intrinsic calculations for Aschbacher–Smith, E.6.8(2), printed
pp.247–248 (PDF pp.258–259 of refs/quasithin.pdf), not the chapter alternative.
-/

public section

open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.BorelActionGeometry
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2]

private noncomputable abbrev coord (s t : F) : Sp F :=
  parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)

private theorem coord_mul (s t u v : F) :
    coord s t * coord u v = coord (s + u) (t + v) := by
  exact congrArg Subtype.val (theta_add s t u v)

private theorem coord_zero : coord (0 : F) 0 = 1 := by
  exact (parameter (F := F)).map_one

private theorem coord_injective {s t u v : F} (h : coord s t = coord u v) :
    s = u ∧ t = v := by
  have he := parameter_injective h
  exact ⟨congrArg (fun x => x.1.toAdd) he, congrArg (fun x => x.2.toAdd) he⟩

private theorem coord_root_zero (s : F) : coord s 0 = rootElement 0 s := by
  simp [coord, parameter_apply, RootSubgroup.element_zero]

private theorem coord_root_four (t : F) : coord 0 t = rootElement 4 t := by
  simp [coord, parameter_apply, RootSubgroup.element_zero]

variable [Finite F]
omit [CharP F 2] in
private theorem exists_unit_ne_one (hF : 2 < Nat.card F) : ∃ c : Fˣ, (c : F) ≠ 1 := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  exact ⟨c, fun he => hc (Units.ext he)⟩

private theorem scale_mem (A : Subgroup (Sp F))
    (hT : (diagonalTorusHom (F := F)).range ≤ normalizer (A : Set (Sp F)))
    {s t : F} (hx : coord s t ∈ A) (c d : Fˣ) :
    coord ((c : F) * s) ((d : F) * t) ∈ A := by
  have hsurj : Function.Surjective (fun a : F => a ^ 2) :=
    Finite.surjective_of_injective CharTwo.sq_injective
  obtain ⟨a, ha⟩ := hsurj c
  have ha0 : a ≠ 0 := by
    intro he
    exact c.ne_zero (by simpa only [he, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] using ha.symm)
  let au : Fˣ := Units.mk0 a ha0
  let bu : Fˣ := d / au
  have hg := hT (show diagonalTorusHom (au, bu) ∈
    (diagonalTorusHom (F := F)).range from ⟨(au, bu), rfl⟩)
  have hh := (mem_normalizer_iff.mp hg (coord s t)).mp hx
  simp only [coord, diagonalTorus_weights] at hh
  have hw : (au : F) * (bu : F) = d := by
    simp only [bu, Units.val_div_eq_div_val]
    exact mul_div_cancel₀ _ au.ne_zero
  simpa only [show (au : F) ^ 2 = (c : F) from ha, hw] using hh

private theorem axis_mem (hF : 2 < Nat.card F) (A : Subgroup (Sp F))
    (hT : (diagonalTorusHom (F := F)).range ≤ normalizer (A : Set (Sp F)))
    {s t : F} (hx : coord s t ∈ A) : coord s 0 ∈ A ∧ coord 0 t ∈ A := by
  obtain ⟨c, hc⟩ := exists_unit_ne_one hF
  have hscaled := scale_mem A hT hx 1 c
  have hsum := A.mul_mem hx hscaled
  simp only [Units.val_one, one_mul, coord_mul, CharTwo.add_self_eq_zero] at hsum
  have hc0 : (1 : F) + c ≠ 0 := by
    intro he
    apply hc
    have he' := eq_neg_of_add_eq_zero_right he
    simpa only [CharTwo.neg_eq] using he'
  have hsecond := scale_mem A hT hsum 1 (Units.mk0 (1 + (c : F)) hc0)⁻¹
  have he : (1 + (c : F))⁻¹ * (t + (c : F) * t) = t := by
    rw [show t + (c : F) * t = (1 + (c : F)) * t by ring,
      inv_mul_cancel_left₀ hc0]
  have hsecond' : coord 0 t ∈ A := by simpa only [mul_zero, Units.val_inv_eq_inv_val,
    Units.val_mk0, he] using hsecond
  have hfirst := A.mul_mem hx hsecond'
  simpa only [coord_mul, add_zero, CharTwo.add_self_eq_zero] using And.intro hfirst hsecond'

private theorem full_first_axis (A : Subgroup (Sp F))
    (hT : (diagonalTorusHom (F := F)).range ≤ normalizer (A : Set (Sp F)))
    {s : F} (hs : s ≠ 0) (hx : coord s 0 ∈ A) : RootSubgroup.group 0 ≤ A := by
  intro x hxroot
  obtain ⟨u, rfl⟩ := (RootSubgroup.mem_group_iff 0 x).mp hxroot
  by_cases hu : u = 0
  · simp [hu, RootSubgroup.element_zero]
  have hh := scale_mem A hT hx (Units.mk0 (u / s) (div_ne_zero hu hs)) 1
  simpa only [Units.val_mk0, Units.val_one, mul_zero, div_mul_cancel₀ _ hs,
    coord_root_zero] using hh

private theorem full_second_axis (A : Subgroup (Sp F))
    (hT : (diagonalTorusHom (F := F)).range ≤ normalizer (A : Set (Sp F)))
    {t : F} (ht : t ≠ 0) (hx : coord 0 t ∈ A) : RootSubgroup.group 4 ≤ A := by
  intro x hxroot
  obtain ⟨u, rfl⟩ := (RootSubgroup.mem_group_iff 4 x).mp hxroot
  by_cases hu : u = 0
  · simp [hu, RootSubgroup.element_zero]
  have hh := scale_mem A hT hx 1 (Units.mk0 (u / t) (div_ne_zero hu ht))
  simpa only [Units.val_mk0, Units.val_one, mul_zero, div_mul_cancel₀ _ ht,
    coord_root_four] using hh

theorem invariant_subgroup_cases (hF : 2 < Nat.card F) (A : Subgroup (Sp F))
    (hA : A ≤ (parameter (F := F)).range)
    (hT : (diagonalTorusHom (F := F)).range ≤ normalizer (A : Set (Sp F))) :
    A = ⊥ ∨ A = RootSubgroup.group 0 ∨ A = RootSubgroup.group 4 ∨
      A = (parameter (F := F)).range := by
  by_cases hfirst : ∃ s t : F, coord s t ∈ A ∧ s ≠ 0
  · obtain ⟨s, t, hx, hs⟩ := hfirst
    have hR0 := full_first_axis A hT hs (axis_mem hF A hT hx).1
    by_cases hsecond : ∃ u v : F, coord u v ∈ A ∧ v ≠ 0
    · obtain ⟨u, v, hy, hv⟩ := hsecond
      have hR4 := full_second_axis A hT hv (axis_mem hF A hT hy).2
      right; right; right
      apply le_antisymm hA
      rintro x ⟨p, rfl⟩
      rw [parameter_apply]
      exact A.mul_mem
        (hR0 ((RootSubgroup.mem_group_iff 0 _).mpr ⟨_, rfl⟩))
        (hR4 ((RootSubgroup.mem_group_iff 4 _).mpr ⟨_, rfl⟩))
    · right; left
      apply le_antisymm _ hR0
      intro x hx
      obtain ⟨p, rfl⟩ := hA hx
      have ht : p.2.toAdd = 0 := by
        by_contra ht
        exact hsecond ⟨p.1.toAdd, p.2.toAdd, hx, ht⟩
      change coord p.1.toAdd p.2.toAdd ∈ RootSubgroup.group 0
      rw [ht, coord_root_zero]
      exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨_, rfl⟩
  · by_cases hsecond : ∃ u v : F, coord u v ∈ A ∧ v ≠ 0
    · obtain ⟨u, v, hy, hv⟩ := hsecond
      have hR4 := full_second_axis A hT hv (axis_mem hF A hT hy).2
      right; right; left
      apply le_antisymm _ hR4
      intro x hx
      obtain ⟨p, rfl⟩ := hA hx
      have hs : p.1.toAdd = 0 := by
        by_contra hs
        exact hfirst ⟨p.1.toAdd, p.2.toAdd, hx, hs⟩
      change coord p.1.toAdd p.2.toAdd ∈ RootSubgroup.group 4
      rw [hs, coord_root_four]
      exact (RootSubgroup.mem_group_iff 4 _).mpr ⟨_, rfl⟩
    · left
      apply le_bot_iff.mp
      intro x hx
      obtain ⟨p, rfl⟩ := hA hx
      have hs : p.1.toAdd = 0 := by
        by_contra hs
        exact hfirst ⟨p.1.toAdd, p.2.toAdd, hx, hs⟩
      have ht : p.2.toAdd = 0 := by
        by_contra ht
        exact hsecond ⟨p.1.toAdd, p.2.toAdd, hx, ht⟩
      apply mem_bot.mpr
      change coord p.1.toAdd p.2.toAdd = 1
      rw [hs, ht, coord_zero]

theorem centralPlane_torus_fixed_eq_bot (hF : 2 < Nat.card F) :
    (parameter (F := F)).range ⊓
      centralizer ((diagonalTorusHom (F := F)).range : Set (Sp F)) = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨⟨p, rfl⟩, hx⟩
  obtain ⟨c, hc⟩ := exists_unit_ne_one hF
  have he (a b : Fˣ) :
      coord ((a : F)^2 * p.1.toAdd) ((a : F) * (b : F) * p.2.toAdd) =
        coord p.1.toAdd p.2.toAdd := by
    dsimp only [coord]
    rw [← diagonalTorus_weights (a,b)]
    change diagonalTorusHom (a,b) * parameter p * (diagonalTorusHom (a,b))⁻¹ = parameter p
    rw [(mem_centralizer_iff.mp hx) _ ⟨(a,b), rfl⟩, mul_inv_cancel_right]
  have ht : p.2.toAdd = 0 := by
    by_contra ht
    have hh := (coord_injective (he 1 c)).2
    apply hc
    apply mul_right_cancel₀ ht
    simpa using hh
  have hs : p.1.toAdd = 0 := by
    by_contra hs
    have hh := (coord_injective (he c 1)).1
    have hh' : (c : F)^2 = 1 := mul_right_cancel₀ hs (by simpa using hh)
    exact hc (CharTwo.sq_injective (by simpa using hh'))
  apply mem_bot.mpr
  change coord p.1.toAdd p.2.toAdd = 1
  rw [hs, ht, coord_zero]

omit [Finite F] in
theorem card_centralPlane : Nat.card (parameter (F := F)).range = Nat.card F ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (parameter_injective (F := F))).toEquiv]
  rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), pow_two]

end Theory.SpecificGroups.SymplecticFour.BorelActionGeometry
