module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.Setup
public import GorensteinWalter.PGammaL2
public import GorensteinWalter.PGammaL2PureSemilinear
public import GorensteinWalter.PGL2KleinFourSelfCentralizer
public import GorensteinWalter.FiniteFieldFixedSubfieldCard

/-!
# A coefficient involution in the square-field fixed action

For a field of order `p² ≡ 9 (mod 16)`, a Sylow two-subgroup of PSL₂
has order divisible by eight. If the faithful four-group action had trivial
field projection, its image in PGL₂ would be a self-centralizing Klein four.
Pointwise fixation would embed the Sylow subgroup into that four-group,
contradicting the order bound.

The actual semilinear coverage and projective Hilbert–90 theorems then
conjugate a nontrivial field actor to the coefficient involution. The fixed
subfield has order `p`, by the Galois cardinality formula. Coverage includes
`p = 3`: the exceptional A₆ automorphisms are accounted for by the same
projective semilinear model, with field and linear projections kept distinct.

This does not identify the fixed subgroup of PSL₂ with PGL₂ over the fixed
field; that projective descent is a separate step.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163, and the numerical cases (6), (8) of F.6.18, pp.309–310.
-/

public section
noncomputable section
open GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields

variable {F A : Type*} [Field F] [Finite F] [Group A] [Finite A]
  [IsElementaryAbelian 2 A]

/-- The square residue excludes the prime two. -/
theorem odd_prime {p : ℕ} (hp : p.Prime) (hm : p ^ 2 % 16 = 9) : Odd p := by
  apply hp.odd_of_ne_two
  intro h
  subst p
  norm_num at hm

omit [Field F] [Finite F] in
/-- The square parameter is an odd prime power. -/
theorem field_odd {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (hm : p ^ 2 % 16 = 9) : IsOddPrimePower (Nat.card F) :=
  ⟨p, 2, hp, odd_prime hp hm, by decide, hF⟩

omit [Field F] [Finite F] in
/-- The square residue gives enough field elements for semilinear coverage. -/
theorem field_large {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (hm : p ^ 2 % 16 = 9) : 3 < Nat.card F := by
  have := hp.two_le
  omega

/-- Every Sylow two-subgroup has order divisible by eight in the square cases. -/
theorem eight_dvd_sylow {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (hm : p ^ 2 % 16 = 9) (P : Sylow 2 (PSL2 F)) : 8 ∣ Nat.card P := by
  have hmod : Nat.card F % 16 = 9 := hF ▸ hm
  have hsq : Nat.card F ^ 2 % 16 = 1 := by rw [Nat.pow_mod, hmod]
  have hd : 16 ∣ Nat.card F ^ 2 - 1 := by omega
  have horder : 8 ∣ Nat.card (PSL2 F) := by
    rw [psl2_card_formula F (field_odd hp hF hm)]
    obtain ⟨k, hk⟩ := hd
    rw [hk]
    have he : Nat.card F * (16 * k) / 2 = 8 * (Nat.card F * k) := by
      rw [show Nat.card F * (16 * k) = 2 * (8 * (Nat.card F * k)) by ring]
      omega
    rw [he]
    exact dvd_mul_right _ _
  exact P.pow_dvd_card_of_pow_dvd_card (n := 3) horder

/-- A faithful four-group fixing the Sylow subgroup has an actor with nontrivial field projection. -/
theorem exists_field_actor {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (hm : p ^ 2 % 16 = 9) (P : Sylow 2 (PSL2 F))
    (ρ : A →* MulAut (PSL2 F)) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4)
    (hfix : ∀ a x, x ∈ (P : Subgroup (PSL2 F)) → ρ a x = x) :
    ∃ (a : A) (x : PGammaL2 F), a ≠ 1 ∧
      pGammaL2ToMulAutPSL2 F (field_odd hp hF hm) (field_large hp hF hm) x = ρ a ∧
      x.right ≠ 1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let π := pGammaL2ToMulAutPSL2 F (field_odd hp hF hm) (field_large hp hF hm)
  let e := MulEquiv.ofBijective π
    ⟨pGammaL2ToMulAutPSL2_injective F _ _,
      pGammaL2ToMulAutPSL2_surjective F hF _ _⟩
  let τ : A →* PGammaL2 F := e.symm.toMonoidHom.comp ρ
  have hτ : Function.Injective τ := e.symm.injective.comp hρ
  have hπτ (a : A) : π (τ a) = ρ a := e.apply_symm_apply _
  by_contra! hnone
  have hright (a : A) : (τ a).right = 1 := by
    by_cases ha : a = 1
    · simp [ha]
    · exact hnone a (τ a) ha (hπτ a)
  let f : A →* PGL2 F := {
    toFun := fun a => (τ a).left
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [map_mul, SemidirectProduct.mul_left, hright, map_one, MulAut.one_apply]
  }
  have hf : Function.Injective f := by
    intro a b h
    apply hτ
    exact SemidirectProduct.ext h (by rw [hright, hright])
  let ef : A ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let : Finite f.range := Finite.of_equiv A ef.toEquiv
  have hfc : Nat.card f.range = 4 := (Nat.card_congr ef.toEquiv).symm.trans hA
  have hfe : Monoid.exponent f.range = 2 := by
    rw [← Monoid.exponent_eq_of_mulEquiv ef]
    have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact IsElementaryAbelian.exponent_eq_prime
  have hfour : IsKleinFour f.range := ⟨hfc, hfe⟩
  have hlinear (a : A) : pgl2InnerAutPSL2 F
      (field_odd hp hF hm) (field_large hp hF hm) (f a) = ρ a := by
    have hinl : SemidirectProduct.inl (f a) = τ a :=
      SemidirectProduct.ext rfl (hright a).symm
    rw [← pGammaL2ToMulAutPSL2_inl, hinl]
    exact hπτ a
  let toPGL : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hcentral (x : P) : toPGL x ∈ Subgroup.centralizer (f.range : Set (PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨a, rfl⟩
    have heq := toPGL_pgl2InnerAutPSL2_apply F
      (field_odd hp hF hm) (field_large hp hF hm) (f a) x
    rw [hlinear, hfix a x x.property] at heq
    change f a * toPGL x = toPGL x * f a
    exact (mul_inv_eq_iff_eq_mul.mp heq.symm)
  have hmem (x : P) : toPGL x ∈ f.range := by
    rw [← pgl2_kleinFour_centralizer_eq_self F (field_odd hp hF hm) f.range hfour]
    exact hcentral x
  have hbound : Nat.card P ≤ 4 := by
    rw [← hfc]
    apply Nat.card_le_card_of_injective (fun x : P => (⟨toPGL x, hmem x⟩ : f.range))
    intro x y h
    apply Subtype.ext
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (congrArg Subtype.val h)
  have hd := eight_dvd_sylow hp hF hm P
  have hpos : 0 < Nat.card P := Nat.card_pos
  have := Nat.le_of_dvd hpos hd
  omega

/-- Some nonidentity actor is projective-linearly conjugate to a coefficient involution. -/
theorem exists_coefficient_actor {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (hm : p ^ 2 % 16 = 9) (P : Sylow 2 (PSL2 F))
    (ρ : A →* MulAut (PSL2 F)) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4)
    (hfix : ∀ a x, x ∈ (P : Subgroup (PSL2 F)) → ρ a x = x) :
    ∃ (a : A) (σ : F ≃+* F) (c : PGL2 F), a ≠ 1 ∧ orderOf σ = 2 ∧
      MulAut.congr (pgl2InnerAutPSL2 F (field_odd hp hF hm)
        (field_large hp hF hm) c)⁻¹ (ρ a) = psl2FieldAut F σ := by
  obtain ⟨a, x, ha, hx, hfield⟩ := exists_field_actor hp hF hm P ρ hρ hA hfix
  let π := pGammaL2ToMulAutPSL2 F (field_odd hp hF hm) (field_large hp hF hm)
  have hpowA : a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have hxpow : x ^ 2 = 1 := by
    apply pGammaL2ToMulAutPSL2_injective F (field_odd hp hF hm) (field_large hp hF hm)
    rw [map_pow, hx, ← map_pow, hpowA, map_one, map_one]
  have hxord : orderOf x = 2 := orderOf_eq_prime hxpow (by
    intro h; apply hfield; rw [h]; rfl)
  have hσpow : x.right ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.right hxpow
    simpa [pow_two] using h
  have hσord : orderOf x.right = 2 := orderOf_eq_prime hσpow hfield
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr
    (field_odd hp hF hm) x hxord hfield
  refine ⟨a, x.right, c, ha, hσord, ?_⟩
  have hc' := congrArg π hc
  simp only [map_mul, map_inv, π, pGammaL2ToMulAutPSL2_inl,
    pGammaL2ToMulAutPSL2_inr, hx] at hc'
  ext y
  exact DFunLike.congr_fun hc' y

omit [Group A] [Finite A] [IsElementaryAbelian 2 A] in
/-- The fixed subfield of an involution of a field of order `p²` has order `p`. -/
theorem fixed_subfield_card {p : ℕ} (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) F) = p := by
  have h := nat_card_eq_fixedSubfield_card_pow_orderOf F σ
  dsimp at h
  rw [hσ, hF] at h
  nlinarith

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields
