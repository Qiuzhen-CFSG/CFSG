module
public import Theory.Character.SemidirectLinearInduction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Four free linear-character orbits for C13 semidirect C3

A nonprincipal linear character of a prime-order group is faithful. Thus a
faithful automorphism action acts freely on its nonprincipal linear characters.
Fourier character counting gives twelve such characters for C13; the free-action
decomposition under a group of order three gives four orbits.

Source: the local exceptional-character construction in
Alperin--Brauer--Gorenstein, III.8, printed pp.116--117.
The orbit enumeration follows the proved construction in
Stellmacher.Recognition.LyonsU3Four.LocalFiveLinearOrbits.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace CyclicThirteenOrbits
variable {P H : Type*} [Group P] [Finite P] [CommGroup H] [Finite H]

omit [Finite P] in
/-- Every nonprincipal linear character of a prime order group is faithful. -/
theorem linear_injective (hP : Nat.card P = 13) (χ : P →* ℂ) (hχ : χ ≠ 1) :
    Function.Injective χ := by
  let : Fact (Nat.card P).Prime := ⟨by rw [hP]; decide⟩
  exact χ.ker_eq_bot_iff.mp ((χ.ker.eq_bot_or_eq_top_of_prime_card).resolve_right
    (fun h => hχ (MonoidHom.ker_eq_top_iff.mp h)))

omit [Finite P] [Finite H] in
theorem orbit_injective (hP : Nat.card P = 13) (α : H →* MulAut P)
    (hα : Function.Injective α) (χ : P →* ℂ) (hχ : χ ≠ 1) :
    Function.Injective (fun a : H => χ.comp (α a).toMonoidHom) := by
  intro a b hab
  apply hα
  ext p
  exact linear_injective hP χ hχ (DFunLike.congr_fun hab p)

omit [Finite H] in
/-- The twelve nonprincipal linear characters form four free triples. -/
theorem exists_four_orbits (hP : Nat.card P = 13) (hH : Nat.card H = 3)
    (α : H →* MulAut P) (hα : Function.Injective α) :
    ∃ ψ : Fin 4 → P →* ℂ,
      (∀ i, ψ i ≠ 1) ∧
      Function.Injective (fun p : Fin 4 × H => (ψ p.1).comp (α p.2).toMonoidHom) ∧
      (∀ χ : P →* ℂ, χ ≠ 1 → ∃ (i : Fin 4) (a : H),
        (ψ i).comp (α a).toMonoidHom = χ) := by
  classical
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let X := {χ : P →* ℂ // χ ≠ 1}
  have hcomp (χ : X) (a : H) : χ.val.comp (α a).toMonoidHom ≠ 1 := by
    intro he
    apply χ.property
    ext s
    have hh := DFunLike.congr_fun he ((α a).symm s)
    simpa using hh
  let : MulAction H X := {
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
  have hstab (χ : X) : MulAction.stabilizer H χ = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply Subgroup.mem_bot.mpr
    apply orbit_injective hP α hα χ.val χ.property
    change a • χ = χ at ha
    have hh := congrArg Subtype.val ha
    change χ.val.comp (α a).toMonoidHom = χ.val at hh
    ext p
    simpa using DFunLike.congr_fun hh p
  have hX : Nat.card X = 12 := by
    let := Fintype.ofFinite (P →* ℂ)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card, AbelianLinearCharacters.card, hP]
    simp
  let O := Quotient (MulAction.orbitRel H X)
  have hO : Nat.card O = 4 := by
    have hc := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
    rw [Nat.card_prod, hX, hH] at hc
    change 12 = Nat.card O * 3 at hc
    omega
  let e : O ≃ Fin 4 := (Finite.equivFin O).trans (finCongr hO)
  let r (i : Fin 4) : X := (e.symm i).out
  let F : Fin 4 × H → X := fun p => p.2 • r p.1
  have hclass (i : Fin 4) (a : H) :
      Quotient.mk (MulAction.orbitRel H X) (F (i,a)) = e.symm i := by
    calc
      _ = Quotient.mk _ (r i) := Quotient.sound
        (show MulAction.orbitRel H X (F (i,a)) (r i) from ⟨a, rfl⟩)
      _ = e.symm i := (e.symm i).out_eq
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i,a⟩ ⟨j,b⟩ he
      have hij : i = j := e.symm.injective ((hclass i a).symm.trans
        ((congrArg (Quotient.mk (MulAction.orbitRel H X)) he).trans (hclass j b)))
      subst j
      have hab : a⁻¹ * b ∈ MulAction.stabilizer H (r i) := by
        change (a⁻¹ * b) • r i = r i
        change a • r i = b • r i at he
        rw [mul_smul, ← he, inv_smul_smul]
      have hab' : a⁻¹ * b = 1 := Subgroup.mem_bot.mp (hstab (r i) ▸ hab)
      exact Prod.ext rfl (inv_mul_eq_one.mp hab')
    · intro χ
      let q : O := Quotient.mk _ χ
      have he : Quotient.mk (MulAction.orbitRel H X) χ =
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

end CyclicThirteenOrbits
