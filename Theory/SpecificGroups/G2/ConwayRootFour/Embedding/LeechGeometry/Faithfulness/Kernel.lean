module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.ScalarFour

/-!
# Reducing the tetrahedral fixed-space kernel to involutions

An operator in characteristic two commuting with a Klein four group and fixing
its common fixed space has fourth power one. For two generators a and b, apply
the fixed-space hypothesis first to b(x)+x for a-fixed x, and then to a(x)+x
for arbitrary x. Faithfulness of the full Leech quotient action transfers this
operator identity to the actual centralizer in the Conway quotient.

Consequently it suffices to exclude kernel involutions. This is a reduction,
not the missing geometric exclusion. An alternative reduction uses the trivial
intersection of the tetrahedral group with its centralizer. We also construct
a U-fixed Leech cross by the odd cardinality of the actual cross set; no source
root-four marking is presumed.

Source: the restricted Leech action in Aschbacher, *Sporadic Groups* (1994),
Lemma 49.5, printed pp.283–284, and the scalar subgroups of Section 48.
The concrete lattices and actions are the attributed ATLAS ports imported by
`ScalarFour`. The binary operator argument here is independent of any Conway
order, simplicity, or involution-class calculation.
-/

public section

open Atlas.Conway Atlas.Codes Atlas.Lattices

private theorem square_fixes_of_fixes_sum {M : Type*} [AddCommGroup M]
    (f : M →+ M) (x : M) (h : f (f x + x) = f x + x) : f (f x) = x := by
  rw [map_add, add_comm (f x) x] at h
  exact add_right_cancel h

/-- Twice applying the displacement of an involution bounds the kernel exponent. -/
private theorem fourth_power_fixed_of_two_involutions
    {M : Type*} [AddCommGroup M] (a b f : M →+ M)
    (hchar : ∀ x : M, x + x = 0)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b x) = x)
    (hab : ∀ x, a (b x) = b (a x))
    (haf : ∀ x, a (f x) = f (a x))
    (hbf : ∀ x, b (f x) = f (b x))
    (hfix : ∀ x, a x = x → b x = x → f x = x) :
    ∀ x, f (f (f (f x))) = x := by
  have hsum (x : M) : a (a x + x) = a x + x := by
    rw [map_add, ha, add_comm]
  have hsquare (x : M) (hx : a x = x) : f (f x) = x := by
    have hwA : a (b x + x) = b x + x := by rw [map_add, hab, hx]
    have hwB : b (b x + x) = b x + x := by rw [map_add, hb, add_comm]
    have hw := hfix (b x + x) hwA hwB
    have hzA : a (f x + x) = f x + x := by rw [map_add, haf, hx]
    have hzB : b (f x + x) = f x + x := by
      rw [map_add, hbf]
      have hw' : f (b x) + f x = b x + x := by simpa only [map_add] using hw
      have hzero : (f (b x) + f x) + (b x + x) = 0 := by rw [hw', hchar]
      have he : (f (b x) + b x) + (f x + x) = 0 := by
        convert hzero using 1
        abel
      have hneg : f (b x) + b x = -(f x + x) := eq_neg_of_add_eq_zero_left he
      have hself : -(f x + x) = f x + x := by
        exact (eq_neg_of_add_eq_zero_left (hchar (f x + x))).symm
      exact hneg.trans hself
    exact square_fixes_of_fixes_sum f x (hfix (f x + x) hzA hzB)
  intro x
  have hax := hsquare (a x + x) (hsum x)
  have hz : a (f (f x) + x) = f (f x) + x := by
    rw [map_add, haf, haf]
    have hx' : f (f (a x)) + f (f x) = a x + x := by
      simpa only [map_add] using hax
    have hzero : (f (f (a x)) + f (f x)) + (a x + x) = 0 := by rw [hx', hchar]
    have he : (f (f (a x)) + a x) + (f (f x) + x) = 0 := by
      convert hzero using 1
      abel
    have hneg := eq_neg_of_add_eq_zero_left he
    exact hneg.trans (eq_neg_of_add_eq_zero_left (hchar (f (f x) + x))).symm
  have hz' := hsquare (f (f x) + x) hz
  apply square_fixes_of_fixes_sum (f.comp f) x
  exact hz'

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry

private theorem U_two_generators :
    ∃ a b : U, ∀ u : U, u = 1 ∨ u = a ∨ u = b ∨ u = a * b := by
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv
    (G₁ := Multiplicative (ZMod 2 × ZMod 2)) (G₂ := U)
  refine ⟨e (Multiplicative.ofAdd (1,0)), e (Multiplicative.ofAdd (0,1)), ?_⟩
  intro u
  obtain ⟨v, rfl⟩ := e.surjective u
  have hv : v = 1 ∨ v = Multiplicative.ofAdd (1,0) ∨
      v = Multiplicative.ofAdd (0,1) ∨
      v = Multiplicative.ofAdd (1,0) * Multiplicative.ofAdd (0,1) := by
    revert v
    decide
  rcases hv with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one e)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul e _ _)))

/-- Every element of the actual restricted-action kernel has fourth power one. -/
theorem kernel_pow_four {g : LeechCentralQuotient} (hg : g ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, quotientModTwoRepresentation g v = v) : g ^ 4 = 1 := by
  obtain ⟨a,b,hab⟩ := U_two_generators
  let ρ := quotientModTwoRepresentation
  have hmul (s t : LeechCentralQuotient) (x : LeechModTwo) : ρ (s*t) x = ρ s (ρ t x) := by
    rw [map_mul]; rfl
  have hinvol (u : U) (x : LeechModTwo) : ρ u (ρ u x) = x := by
    rw [← hmul]
    have he : (u : LeechCentralQuotient) * u = 1 := congrArg Subtype.val (IsKleinFour.mul_self u)
    rw [he, map_one]; rfl
  have hcomm (u v : U) (x : LeechModTwo) : ρ u (ρ v x) = ρ v (ρ u x) := by
    rw [← hmul, ← hmul]
    have he : (u : LeechCentralQuotient) * v = v * u := congrArg Subtype.val (mul_comm_of_exponent_two IsKleinFour.exponent_two u v)
    rw [he]
  have hcommg (u : U) (x : LeechModTwo) : ρ u (ρ g x) = ρ g (ρ u x) := by
    rw [← hmul, ← hmul, hg u (U_le_I u.property)]
  have hall (x : LeechModTwo) (ha : ρ a x = x) (hb : ρ b x = x) : x ∈ fixedSpace := by
    intro u hu
    rcases hab ⟨u,hu⟩ with he | he | he | he
    · have he' : u = 1 := congrArg Subtype.val he
      rw [he', map_one]; rfl
    · have he' : u = a := congrArg Subtype.val he
      rw [he']; exact ha
    · have he' : u = b := congrArg Subtype.val he
      rw [he']; exact hb
    · have he' : u = a * b := congrArg Subtype.val he
      rw [he', hmul, hb, ha]
  have hfour := fourth_power_fixed_of_two_involutions
    (ρ a).toLinearMap.toAddMonoidHom (ρ b).toLinearMap.toAddMonoidHom
    (ρ g).toLinearMap.toAddMonoidHom
    (fun x => by
      have hz : (2 : Bit) = 0 := by decide
      simpa only [two_smul, zero_smul] using congrArg (fun c : Bit => c • x) hz)
    (hinvol a) (hinvol b) (hcomm a b) (hcommg a) (hcommg b)
    (fun x ha hb => hfix x (hall x ha hb))
  apply quotientModTwoRepresentation_injective
  apply LinearEquiv.ext
  intro x
  change ρ (g^4) x = ρ 1 x
  have he : g ^ 4 = g * (g * (g * g)) := by simp [pow_succ, mul_assoc]
  rw [he, hmul, hmul, hmul, map_one]
  exact hfour x

/-- A tetrahedral group has trivial intersection with its ambient centralizer. -/
theorem eq_one_of_mem_centralizerI_of_mem_I {g : LeechCentralQuotient}
    (hg : g ∈ centralizerI) (hI : g ∈ I) : g = 1 := by
  obtain ⟨a, rfl⟩ := hI
  have ha : a ∈ Subgroup.center (alternatingGroup fourPoints) := by
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply scalarFour_injective
    simpa only [map_mul] using hg (scalarFour b) ⟨b, rfl⟩
  rw [alternatingGroup.center_eq_bot (by rw [fourPoints_card])] at ha
  simp only [Subgroup.mem_bot.mp ha, map_one]

/-- A geometric bound by U would discharge the requested faithful action. -/
theorem centralizerFaithful_of_kernel_le_U
    (hU : ∀ g ∈ centralizerI,
      (∀ v ∈ fixedSpace, quotientModTwoRepresentation g v = v) → g ∈ U) :
    CentralizerFaithful := by
  intro g hg hfix
  exact eq_one_of_mem_centralizerI_of_mem_I hg (U_le_I (hU g hg hfix))

/-- The only geometric exclusions needed after `kernel_pow_four` are involutions. -/
theorem centralizerFaithful_of_involution_kernel
    (htwo : ∀ g ∈ centralizerI,
      (∀ v ∈ fixedSpace, quotientModTwoRepresentation g v = v) → g ^ 2 = 1 → g = 1) :
    CentralizerFaithful := by
  intro g hg hfix
  have hfour := kernel_pow_four hg hfix
  have hfix2 : ∀ v ∈ fixedSpace, quotientModTwoRepresentation (g ^ 2) v = v := by
    intro v hv
    rw [pow_two, map_mul]
    change quotientModTwoRepresentation g (quotientModTwoRepresentation g v) = v
    rw [hfix v hv, hfix v hv]
  have hsquare : g ^ 2 = 1 := htwo (g ^ 2) (centralizerI.pow_mem hg 2) hfix2 (by
    simpa only [← pow_mul] using hfour)
  exact htwo g hg hfix hsquare

/-- A cross fixed by U exists without identifying the source root-four class:
the number of actual Leech crosses is odd. -/
theorem exists_fixedCross : ∃ X : LeechCross, X.val ∈ fixedSpace := by
  let action : U →* Equiv.Perm LeechCross := quotientCrossRepresentation.comp U.subtype
  let : MulAction U LeechCross := MulAction.compHom LeechCross action
  have hU : IsPGroup 2 U := IsPGroup.of_card (n := 2) U_card
  obtain ⟨X,hX⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card LeechCross (by
    rw [leechCross_card]
    decide)
  refine ⟨X, ?_⟩
  intro u hu
  have he : quotientCrossRepresentation u X = X := MulAction.mem_fixedPoints.mp hX ⟨u,hu⟩
  have hv := congrArg Subtype.val he
  rwa [quotientCross_modTwo_equivariant] at hv

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
