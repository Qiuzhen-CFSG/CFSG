module

public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.LinearFactor
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation
public import Theory.GroupAction.CubicBorelRigidity

/-!
# Cubic Borel rigidity for nonbinary SL₃

An automorphism of order dividing three which preserves a Sylow two-subgroup
and fixes its full normalizer quotient is trivial when the normalizer has
order prime to three. We first conjugate the specified Sylow to the upper
unitriangular subgroup. Binary projective automorphism coverage lifts through
the faithful central-quotient action to the actual special linear carrier.

The diagonal subgroup embeds the field units in the Borel, so the unit-group
order is prime to three. Triangularity removes the linear factor from the
full torus calculation. The faithful first axis detects every field
contribution; a graph contribution would force every unit to be cubic and
hence trivial. A power equal to the unit-group order makes a linear actor
inner, so coprimality makes the cubic actor itself inner. Its conjugating
element normalizes the Sylow, and the normalizer-order bound kills its action.
The projective parameter comparison retains the actual cubic scalar kernel;
no identification of SL₃ with PSL₃ or centerlessness is assumed.

Source: GLS3, Theorem 2.5.12 and §2.7,
`refs/KGroup/GLS3/chapter2.tex`; the intrinsic calculation used in
Aschbacher–Smith, `refs/quasithin.pdf`, printed p.1144, proof of 15.3.49(k).
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
namespace Matrix.PSL3.CubicBorelRigidity

private theorem map_eq_of_stable {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (α : MulAut G) (h : ∀ x ∈ H, α x ∈ H) :
    H.map α.toMonoidHom = H := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  · exact (Subgroup.card_map_of_injective α.injective).ge

private theorem inner_cubic_eq_one {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hN : ¬ 3 ∣ Nat.card (normalizer (H : Set G)))
    (α : MulAut G) (hα : α ^ 3 = 1) (hstable : H.map α.toMonoidHom = H)
    (hinner : α ∈ MulAut.innerSubgroup G) : α = 1 := by
  obtain ⟨g,hg⟩ := hinner
  have hgN : g ∈ normalizer (H : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, hg]
    exact hstable
  let x : normalizer (H : Set G) := ⟨g,hgN⟩
  let f : normalizer (H : Set G) →* MulAut G :=
    MulAut.conj.comp (normalizer (H : Set G)).subtype
  have hx : f x = α := hg
  have hd : orderOf α ∣ Nat.card (normalizer (H : Set G)) := by
    rw [← hx]
    exact (orderOf_map_dvd f x).trans (orderOf_dvd_natCard x)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hN)
    (orderOf_dvd_of_pow_eq_one hα) hd)

variable (F : Type*) [Field F] [Finite F]

private theorem units_three_free (hB : ¬ 3 ∣ Nat.card (borelSL F)) :
    ¬ 3 ∣ Nat.card Fˣ := by
  let f : Fˣ →* borelSL F := {
    toFun := fun a => ⟨torusSL F (a,1), torusSL_mem_borel F (a,1)⟩
    map_one' := Subtype.ext (map_one (torusSL F))
    map_mul' := fun a b => Subtype.ext (by
      simpa only [Subgroup.coe_mul, Prod.mk_mul_mk, one_mul] using map_mul (torusSL F) (a,1) (b,1)) }
  have hf : Function.Injective f := by
    intro a b h
    exact congrArg Prod.fst (torusSL_injective F (congrArg Subtype.val h))
  exact fun h => hB (h.trans (card_dvd_of_injective f hf))

/-- Standard coverage on the actual special linear carrier. -/
theorem specialCoverage {e : ℕ} (he : 1 < e) (hF : Nat.card F = 2 ^ e) :
    SpecialCoverage F := by
  apply ActorCoverage.specialCoverage_of_standard_eq_top
  exact Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation F
    (by omega) hF (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots
      F he hF)

private theorem standard_cubic_eq_one [CharP F 2] {e : ℕ}
    (he : 1 < e) (hF : Nat.card F = 2 ^ e)
    (hB : ¬ 3 ∣ Nat.card (borelSL F))
    (α : MulAut SL(3,F)) (hα : α ^ 3 = 1)
    (hstable : (unipotentSL F).map α.toMonoidHom = unipotentSL F)
    (hfix : ∀ b ∈ borelSL F, α b * b⁻¹ ∈ unipotentSL F) : α = 1 := by
  have hu3 := units_three_free F hB
  have hcop : Nat.Coprime 3 (Nat.card Fˣ) :=
    (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hu3
  obtain ⟨m,σ,ε,rfl⟩ := specialCoverage F he hF α
  have hps := centerAction_unipotent F _ hstable
  rw [centerAction_specialActor] at hps
  have hm := NormalizerForm.linearConj_upperTriangular F m
    (linear_part_unipotent F m σ ε hps)
  have hfix' (u : Fˣ) :
      projectiveActor F m σ ε (torusMap F (u,1)) * (torusMap F (u,1))⁻¹ ∈
        unipotent F := by
    have hh := mem_map_of_mem (projection F)
      (hfix (torusSL F (u,1)) (torusSL_mem_borel F (u,1)))
    rw [map_mul, map_inv] at hh
    change centerAction F (specialActor F m σ ε) (torusMap F (u,1)) * _ ∈ _ at hh
    rwa [centerAction_specialActor] at hh
  cases ε
  · have hσ : σ = 1 := by
      apply RingEquiv.ext
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · let u : Fˣ := Units.mk0 x hx
        have hh := hfix' u
        simp only [projectiveActor, Bool.false_eq_true, ↓reduceIte, mul_one,
          MulAut.mul_apply, field_torusMap, map_one] at hh
        have hp := ResidualLinear.parameters_eq_of_displacement m hm _ _ hh
        exact congrArg Units.val (ResidualParameters.projective_axis_injective hp)
    have ha : specialActor F m σ false = linearConjSL F m := by
      have hf : Atlas.fieldEquivSL 3 (1 : F ≃+* F) = 1 := by
        ext g i j
        rfl
      simp [specialActor, hσ, hf]
    rw [ha] at hα hstable ⊢
    have hi : linearConjSL F m ∈ MulAut.innerSubgroup SL(3,F) := by
      obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime
        (hcop.symm.of_dvd_right (orderOf_dvd_of_pow_eq_one hα))
      rw [← hk]
      exact (MulAut.innerSubgroup SL(3,F)).pow_mem (linearConjSL_pow_inner F m) k
    apply inner_cubic_eq_one (unipotentSL F) _ _ hα hstable hi
    rwa [normalizer_unipotentSL]
  · have hall : ∀ u : Fˣ, u = 1 := by
      intro u
      have hh := hfix' u
      simp only [projectiveActor, ↓reduceIte, MulAut.mul_apply,
        oppositionGraph_torusMap, field_torusMap, inv_one, map_one, map_inv] at hh
      have hp := ResidualLinear.parameters_eq_of_displacement m hm _ _ hh
      have hu := ResidualParameters.cube_eq_one_of_graph_field_axis σ u hp
      exact hcop.symm.pow_left_bijective.injective (by simpa using hu)
    have : Subsingleton Fˣ := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have hc := Nat.card_unique (α := Fˣ)
    rw [Nat.card_units, hF] at hc
    have hp : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Cubic rigidity on SL₃ over every nonbinary field of characteristic two.
The normalizer is that of the specified Sylow subgroup. -/
theorem specialLinear {e : ℕ} (he : 1 < e) (hF : Nat.card F = 2 ^ e) :
    MulAut.CubicBorelRigid SL(3,F) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := e)
    (by simpa only [← Nat.card_eq_fintype_card] using hF)
  intro P hN α hα hP hB
  obtain ⟨g,hgU,hgB⟩ := sylowSL_normalizer_conjugate F (by omega) hF P
  let c := MulAut.conj g
  have hmem (x : SL(3,F)) : c x ∈ P ↔ x ∈ unipotentSL F := by
    change c x ∈ (P : Subgroup SL(3,F)) ↔ _
    rw [← hgU, mem_map_equiv]
    exact iff_of_eq (congrArg (fun y => y ∈ unipotentSL F) (c.symm_apply_apply x))
  have hthree : ¬ 3 ∣ Nat.card (borelSL F) := by
    rwa [← Nat.card_congr (sylowSLNormalizerEquiv F (by omega) hF P).toEquiv]
  let β := MulAut.congr c.symm α
  have hb3 : β ^ 3 = 1 := by
    change (MulAut.congr c.symm α) ^ 3 = 1
    rw [← map_pow, hα, map_one]
  have hbP : (unipotentSL F).map β.toMonoidHom = unipotentSL F := by
    apply map_eq_of_stable
    intro x hx
    apply (hmem (β x)).mp
    change c (c.symm (α (c x))) ∈ P
    rw [c.apply_symm_apply]
    exact hP _ ((hmem x).mpr hx)
  have hbB : ∀ b ∈ borelSL F, β b * b⁻¹ ∈ unipotentSL F := by
    intro b hb
    apply (hmem _).mp
    rw [map_mul, map_inv]
    change c (c.symm (α (c b))) * (c b)⁻¹ ∈ P
    rw [c.apply_symm_apply]
    apply hB
    rw [← hgB]
    exact mem_map_of_mem c.toMonoidHom hb
  have hβ := standard_cubic_eq_one F he hF hthree β hb3 hbP hbB
  exact (MulAut.congr c.symm).injective (hβ.trans (map_one _).symm)

end Matrix.PSL3.CubicBorelRigidity
