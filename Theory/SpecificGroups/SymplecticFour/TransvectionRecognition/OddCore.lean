module

public import Theory.Representation.NormalOddQuadratic
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.NormalClosure
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.CComponent.FittingCentralizer

/-!
# Odd cores from the actual quadratic-form exclusion

An irreducible symplectic subgroup has no fixed vectors for a nontrivial
normal subgroup. An odd normal subgroup would therefore give a unique
invariant quadratic refinement by averaging. Normality makes the full group
preserve that refinement. Thus a subgroup excluded from every compatible
orthogonal group has trivial odd core; trivial two-core then gives F=1,
also for its normal transvection closure.

This is the source-specialized alternative to the odd-Fitting argument in
Aschbacher--Smith G.4.9, printed p.341. The actual E.2.7 application discharges
the quadratic exclusion from the original moving central subgroup.
-/

public noncomputable section

open Subgroup Matrix

namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition

variable {F : Type*} [Field F] [CharP F 2]

/-- A fixed refinement of the standard alternating form. -/
def standardQuadratic : QuadraticForm F (Vector F) :=
  QuadraticMap.proj (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) +
    QuadraticMap.proj (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))

theorem standardQuadratic_polar : (standardQuadratic (F := F)).polarBilin = form F := by
  apply LinearMap.ext₂
  intro x y
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    standardQuadratic,_root_.add_apply,QuadraticMap.proj_apply,
    Pi.add_apply,form_apply,Fin.sum_univ_two,CharTwo.sub_eq_add]
  ring_nf
  simp only [CharTwo.two_eq_zero,mul_zero,zero_add,add_zero]

omit [CharP F 2] in
private theorem natural_faithful (H : Subgroup (Sp F)) :
    Function.Injective ((Representation.symplecticNatural 2).comp H.subtype) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun f : Module.End F (Vector F) => f (Pi.single j 1) i) he
  change ((g : Sp F).val *ᵥ Pi.single j 1) i = ((h : Sp F).val *ᵥ Pi.single j 1) i at hh
  simpa using hh

/-- In an irreducible literal subgroup, a nontrivial odd normal subgroup
would force an invariant compatible quadratic form. -/
theorem normal_odd_eq_bot_of_no_invariant_quadratic
    (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (hno : ∀ Q : QuadraticForm F (Vector F), Q.polarBilin = form F →
      ¬ ∀ g ∈ H, ∀ v : Vector F, Q (g • v) = Q v)
    (N : Subgroup H) [N.Normal] [Finite N] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_contra hn
  let ρ : Representation F H (Vector F) := (Representation.symplecticNatural 2).comp H.subtype
  let : ρ.IsIrreducible := hi
  have hfix := Representation.RankOneSymplectic.normal_invariants_eq_bot ρ
    (natural_faithful H) N hn
  obtain ⟨Q,hQ,hpres⟩ := Representation.NormalOddQuadratic.exists_invariant_of_odd_normal
    ρ N hodd hfix (standardQuadratic (F := F)) (fun g x y => by
      rw [standardQuadratic_polar]
      exact preserves_form (g : Sp F) x y)
  exact hno Q (hQ.trans standardQuadratic_polar) (fun g hg => hpres ⟨g,hg⟩)

variable [Finite F]

/-- The quadratic exclusion kills the entire odd core, including when H
contains transvections. -/
theorem oddCore_eq_bot_of_no_invariant_quadratic
    (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (hno : ∀ Q : QuadraticForm F (Vector F), Q.polarBilin = form F →
      ¬ ∀ g ∈ H, ∀ v : Vector F, Q (g • v) = Q v) :
    pPrimeCore 2 H = ⊥ := by
  apply normal_odd_eq_bot_of_no_invariant_quadratic H hi hno
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))

/-- The actual pair's two-core and orthogonal exclusion eliminate its
Fitting subgroup. -/
theorem fitting_eq_bot_of_no_invariant_quadratic
    (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (h2 : pCore 2 H = ⊥)
    (hno : ∀ Q : QuadraticForm F (Vector F), Q.polarBilin = form F →
      ¬ ∀ g ∈ H, ∀ v : Vector F, Q (g • v) = Q v) :
    fittingSubgroup H = ⊥ := by
  exact le_bot_iff.mp ((fitting_le_pPrimeCore_of_pCore_eq_bot 2 h2).trans_eq
    (oddCore_eq_bot_of_no_invariant_quadratic H hi hno))

/-- The Fitting subgroup of every normal subgroup vanishes, in particular
that of the literal F-transvection closure. -/
theorem normal_fitting_eq_bot_of_no_invariant_quadratic
    (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (h2 : pCore 2 H = ⊥)
    (hno : ∀ Q : QuadraticForm F (Vector F), Q.polarBilin = form F →
      ¬ ∀ g ∈ H, ∀ v : Vector F, Q (g • v) = Q v)
    (N : Subgroup H) [N.Normal] : fittingSubgroup N = ⊥ := by
  apply (map_eq_bot_iff_of_injective _ N.subtype_injective).mp
  apply le_bot_iff.mp
  exact (fittingSubgroup_map_subtype_le_of_isSubnormal N
    (inferInstance : N.Normal).isSubnormal).trans_eq
      (fitting_eq_bot_of_no_invariant_quadratic H hi h2 hno)

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
