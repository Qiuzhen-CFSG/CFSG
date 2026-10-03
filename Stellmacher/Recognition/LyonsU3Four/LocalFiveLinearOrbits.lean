module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveLinearCharacters
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The three nonprincipal linear-character orbits in the Lyons Sylow group

The sixteen linear characters are the characters of the abelianization, whose
order is sixteen. Precomposition by the complement acts freely on the fifteen
nonprincipal characters: a nonidentity stabilizer would contain the complement
generator, and the displacement argument in `LocalFiveLinearCharacters` would
make the character principal. The free-action decomposition then gives three
representatives, with unique complement coordinates for every nonprincipal
character. Every such character kills the center because it is the commutator
subgroup.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 2,
p. 373, and the degree-five construction in Lemma 4, p. 381.
-/

public section
open scoped BigOperators IsMulCommutative
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four

private def linearAbelianizationEquiv (H : Type*) [Group H] :
    (H →* ℂ) ≃ (Abelianization H →* ℂ) :=
  MonoidHom.toHomUnitsMulEquiv.toEquiv.trans
    (Abelianization.lift.trans MonoidHom.toHomUnitsMulEquiv.toEquiv.symm)

/-- There are sixteen complex linear characters of the intrinsic Sylow group. -/
theorem sylowLinear_card {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) : Nat.card (S →* ℂ) = 16 := by
  let : Finite (Abelianization S) := inferInstanceAs (Finite (S ⧸ commutator S))
  rw [Nat.card_congr (linearAbelianizationEquiv S), AbelianLinearCharacters.card]
  change Nat.card (S ⧸ commutator S) = 16
  rw [← h.center_eq_commutator]
  exact center_quotient_card S h

/-- Exactly fifteen of the Sylow group's linear characters are nonprincipal. -/
theorem sylowNonprincipalLinear_card {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) :
    Nat.card {χ : S →* ℂ // χ ≠ 1} = 15 := by
  classical
  let : Finite (Abelianization S) := inferInstanceAs (Finite (S ⧸ commutator S))
  let : Finite (S →* ℂ) := Finite.of_equiv (Abelianization S →* ℂ)
    (linearAbelianizationEquiv S).symm
  let := Fintype.ofFinite (S →* ℂ)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, sylowLinear_card S h]
  simp

/-- Every linear character kills the center, which is the commutator subgroup. -/
theorem sylowLinear_center {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) (χ : S →* ℂ)
    (z : Subgroup.center S) : χ z = 1 := by
  have hz : (z : S) ∈ commutator S := h.center_eq_commutator ▸ z.property
  exact congrArg Units.val (Abelianization.commutator_subset_ker χ.toHomUnits hz)

/-- The fifteen nonprincipal characters split into three free complement orbits. -/
theorem exists_three_linear_orbits {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ)) :
    ∃ ψ : Fin 3 → S →* ℂ,
      (∀ i, ψ i ≠ 1) ∧
      Function.Injective (fun p : Fin 3 × FiveComplement =>
        (ψ p.1).comp (α p.2).toMonoidHom) ∧
      (∀ χ : S →* ℂ, χ ≠ 1 → ∃ (i : Fin 3) (a : FiveComplement),
        (ψ i).comp (α a).toMonoidHom = χ) := by
  classical
  let : Finite (Abelianization S) := inferInstanceAs (Finite (S ⧸ commutator S))
  let : Finite (S →* ℂ) := Finite.of_equiv (Abelianization S →* ℂ)
    (linearAbelianizationEquiv S).symm
  let X := {χ : S →* ℂ // χ ≠ 1}
  have hcomp (χ : X) (a : FiveComplement) : χ.val.comp (α a).toMonoidHom ≠ 1 := by
    intro he
    apply χ.property
    ext s
    have hh := DFunLike.congr_fun he ((α a).symm s)
    simpa using hh
  let : MulAction FiveComplement X := {
    smul a χ := ⟨χ.val.comp (α a).toMonoidHom, hcomp χ a⟩
    one_smul χ := by
      apply Subtype.ext
      ext s
      change χ.val (α 1 s) = χ.val s
      simp
    mul_smul a b χ := by
      apply Subtype.ext
      ext s
      change χ.val (α (a * b) s) = χ.val (α b (α a s))
      rw [mul_comm a b, map_mul]
      rfl }
  have hcard : Nat.card FiveComplement = 5 := by
    simp [FiveComplement, Nat.card_eq_fintype_card]
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hstab (χ : X) : MulAction.stabilizer FiveComplement χ = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply Subgroup.mem_bot.mpr
    by_contra hane
    have ht : MulAction.stabilizer FiveComplement χ = ⊤ := by
      apply top_unique
      rw [← zpowers_eq_top_of_prime_card hcard hane]
      exact Subgroup.zpowers_le.mpr ha
    have hg : (Multiplicative.ofAdd (1 : ZMod 5)) • χ = χ :=
      show Multiplicative.ofAdd (1 : ZMod 5) ∈ MulAction.stabilizer FiveComplement χ from
        ht ▸ Subgroup.mem_top _
    have hinv (s : S) : χ.val.toHomUnits ((β ^ (3 : ℕ)) s) = χ.val.toHomUnits s := by
      apply Units.ext
      have hh := DFunLike.congr_fun (congrArg Subtype.val hg) s
      change χ.val (α (Multiplicative.ofAdd 1) s) = χ.val s at hh
      simpa only [hα, MonoidHom.coe_toHomUnits] using hh
    apply χ.property
    ext s
    exact congrArg Units.val (cube_invariant_linear_eq_one S h β hβ χ.val.toHomUnits hinv s)
  have hX : Nat.card X = 15 := sylowNonprincipalLinear_card S h
  let O := Quotient (MulAction.orbitRel FiveComplement X)
  have hO : Nat.card O = 3 := by
    have hc := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
    rw [Nat.card_prod, hX, hcard] at hc
    change 15 = Nat.card O * 5 at hc
    omega
  let := Fintype.ofFinite O
  let e : O ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hO)
  let r (i : Fin 3) : X := (e.symm i).out
  let F : Fin 3 × FiveComplement → X := fun p => p.2 • r p.1
  have hclass (i : Fin 3) (a : FiveComplement) :
      Quotient.mk (MulAction.orbitRel FiveComplement X) (F (i,a)) = e.symm i := by
    calc
      _ = Quotient.mk _ (r i) := Quotient.sound (show MulAction.orbitRel FiveComplement X (F (i,a)) (r i) from ⟨a, rfl⟩)
      _ = e.symm i := (e.symm i).out_eq
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i,a⟩ ⟨j,b⟩ he
      have hij : i = j := e.symm.injective ((hclass i a).symm.trans
        ((congrArg (Quotient.mk (MulAction.orbitRel FiveComplement X)) he).trans (hclass j b)))
      subst j
      have hab : a⁻¹ * b ∈ MulAction.stabilizer FiveComplement (r i) := by
        change (a⁻¹ * b) • r i = r i
        change a • r i = b • r i at he
        rw [mul_smul, ← he, inv_smul_smul]
      have hab' : a⁻¹ * b = 1 := Subgroup.mem_bot.mp (hstab (r i) ▸ hab)
      exact Prod.ext rfl (inv_mul_eq_one.mp hab')
    · intro χ
      let q : O := Quotient.mk _ χ
      have he : Quotient.mk (MulAction.orbitRel FiveComplement X) χ =
          Quotient.mk _ (r (e q)) := by
        change q = Quotient.mk _ ((e.symm (e q)).out)
        rw [e.symm_apply_apply, Quotient.out_eq]
      obtain ⟨a, ha⟩ := Quotient.exact he
      exact ⟨(e q, a), ha⟩
  refine ⟨fun i => (r i).val, fun i => (r i).property, ?_, ?_⟩
  · intro p q he
    exact hF.1 (Subtype.ext he)
  · intro χ hχ
    obtain ⟨⟨i,a⟩, he⟩ := hF.2 ⟨χ,hχ⟩
    exact ⟨i,a,congrArg Subtype.val he⟩

/-- No complement element is repeated in a nonprincipal character's orbit. -/
theorem sylowLinear_orbit_injective {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (χ : S →* ℂ) (hχ : χ ≠ 1) :
    Function.Injective (fun a : FiveComplement => χ.comp (α a).toMonoidHom) := by
  obtain ⟨ψ, _, hinj, hfull⟩ := exists_three_linear_orbits S h β hβ α hα
  obtain ⟨i,b,rfl⟩ := hfull χ hχ
  intro a c hac
  have he : (ψ i).comp (α (b * a)).toMonoidHom =
      (ψ i).comp (α (b * c)).toMonoidHom := by
    ext s
    change ψ i (α (b * a) s) = ψ i (α (b * c) s)
    rw [map_mul, map_mul]
    exact DFunLike.congr_fun hac s
  have hp := congrArg Prod.snd (hinj (show
    (ψ (i,b*a).1).comp (α (i,b*a).2).toMonoidHom =
      (ψ (i,b*c).1).comp (α (i,b*c).2).toMonoidHom from he))
  exact mul_left_cancel hp

/-- Each of the fifteen nonprincipal characters has an orbit of size five. -/
theorem sylowLinear_orbit_card {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (χ : S →* ℂ) (hχ : χ ≠ 1) :
    (Set.range (fun a : FiveComplement => χ.comp (α a).toMonoidHom)).ncard = 5 := by
  rw [Set.ncard_range_of_injective (sylowLinear_orbit_injective S h β hβ α hα χ hχ)]
  simp [FiveComplement, Nat.card_eq_fintype_card]

end Stellmacher.Recognition.LyonsU3Four
