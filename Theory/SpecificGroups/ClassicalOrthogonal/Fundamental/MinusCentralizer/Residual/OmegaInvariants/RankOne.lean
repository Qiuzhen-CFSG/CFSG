module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Elementary generation on the actual minus four-space

The full orthogonal commutator on the chosen minus four-space is simple:
semilinear quadratic transport identifies it with the Hermitian commutator,
and the actual SL₂ congruence map is onto that commutator with kernel exactly
the SL₂ center. A nonfixed element of the quadratic field supplies the
hypothesis of PSL₂ simplicity. All field and quadratic-transport premises are
provided by the existing finite-field comparison.

The elementary subgroup is normal in the full isometry group and, in odd
characteristic, lies in its commutator. The Siegel transformation along the
first hyperbolic direction with parameter `(0, (1, 0))` moves the first
anisotropic coordinate of its hyperbolic partner from zero to minus one.
Thus its restriction to the simple commutator is nontrivial and hence the
whole commutator. This proves the Witt-index-one endpoint, including F₃,
without a second hyperbolic pair or a generation assumption.

This discharges the rank-one elementary-generation premise of the minus
complement residual assembly in Aschbacher–Smith A.2.17, printed p.39
(`refs/quasithin.pdf`). The full-isometry commutator and scalar conventions
are those of GLS3 §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open ClassicalOrthogonal.Quadratic
open Minus.OddFourComparison
open ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
universe u

private theorem hermitianOmega_simple {E : Type u} [Field E] [Finite E]
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (hdim : Module.finrank (HermitianModel.fixedField σ) E = 2)
    (hne : ∃ t : E, σ t ≠ t) :
    IsSimpleGroup (Minus.Omega (HermitianModel.fixedField σ)
      (HermitianModel.Space σ hσ) (HermitianModel.minusForm σ hσ)) := by
  let e := (MulEquiv.subgroupCongr
    (HermitianModel.range_orthogonalAction_eq_commutator σ hσ hdim hne)).symm.trans
      ((QuotientGroup.quotientKerEquivRange (HermitianModel.orthogonalAction σ hσ)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq (HermitianModel.orthogonalAction_ker σ hσ)))
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) := by
    apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
    obtain ⟨t, ht⟩ := hne
    refine ⟨t, ?_, ?_⟩
    · rintro rfl
      exact ht (map_zero σ)
    · intro h
      rcases sq_eq_one_iff.mp h with h | h
      · exact ht (by rw [h, map_one])
      · exact ht (by rw [h, map_neg, map_one])
  exact e.isSimpleGroup

/-- The literal minus-four commutator is simple, before taking any scalar quotient. -/
theorem rankOne_omega_simple (F : Type u) [Field F] [Finite F] :
    IsSimpleGroup (Minus.Omega F (Minus.Space F 1) (Minus.quadraticForm F 2)) := by
  obtain ⟨E, hE, hfin, σ, hσ, _, _, hdim, hne, s, e, he, _⟩ :=
    QuadraticTransport.exists_comparison F
  have := hermitianOmega_simple σ hσ hdim hne
  exact (omegaSemilinearCongr s e he).isSimpleGroup

variable {F : Type u} [Field F] [Finite F]
private abbrev direction : Minus.Space F 1 := (fun _ => (1, 0), (0, 0))
private abbrev partner : Minus.Space F 1 := (fun _ => (0, 1), (0, 0))
private abbrev transverse : Minus.Space F 1 := (0, (1, 0))

private theorem direction_singular : Minus.quadraticForm F 2 (direction (F := F)) = 0 := by
  simp [Minus.quadraticForm, direction]

private theorem direction_perp :
    (Minus.quadraticForm F 2).polarBilin (direction (F := F)) transverse = 0 := by
  change (Minus.form F 1 (Minus.parameter F)).polarBilin _ _ = 0
  rw [Minus.form_polar, Minus.plane_polar]
  simp

private def witness : quadraticIsometrySubgroup (Minus.quadraticForm F 2) :=
  siegelElement _ direction transverse direction_singular direction_perp

private theorem witness_ne_one : witness (F := F) ≠ 1 := by
  intro h
  have hh := congrArg
    (fun g : quadraticIsometrySubgroup (Minus.quadraticForm F 2) => (g.val partner).2.1) h
  change (siegel (Minus.quadraticForm F 2) direction transverse partner).2.1 = _ at hh
  have hp : (Minus.quadraticForm F 2).polarBilin (partner (F := F)) direction = 1 := by
    change (Minus.form F 1 (Minus.parameter F)).polarBilin _ _ = 1
    rw [Minus.form_polar, Minus.plane_polar]
    simp
  have ht : (Minus.quadraticForm F 2).polarBilin (partner (F := F)) transverse = 0 := by
    change (Minus.form F 1 (Minus.parameter F)).polarBilin _ _ = 0
    rw [Minus.form_polar, Minus.plane_polar]
    simp
  simp [siegel, hp, ht, partner, direction, transverse] at hh

/-- Every full-isometry commutator on the actual minus four-space is elementary. -/
theorem rankOne_commutator_le_elementary (h2 : (2 : F) ≠ 0) :
    commutator (quadraticIsometrySubgroup (Minus.quadraticForm F 2)) ≤
      elementarySubgroup (Minus.quadraticForm F 2) := by
  let D := Minus.Omega F (Minus.Space F 1) (Minus.quadraticForm F 2)
  let N := (elementarySubgroup (Minus.quadraticForm F 2)).subgroupOf D
  have : IsSimpleGroup D := rankOne_omega_simple F
  have hnormal : N.Normal := (SplitOddBlocks.elementary_normal _).subgroupOf D
  have hne : N ≠ ⊥ := by
    intro hz
    have hw : witness (F := F) ∈ elementarySubgroup (Minus.quadraticForm F 2) :=
      siegelElement_mem _ _ _ _ _
    let w : D := ⟨witness, complement_elementary_le_omega 1 (by decide) h2 hw⟩
    have hn : w ∈ N := hw
    rw [hz, Subgroup.mem_bot] at hn
    exact witness_ne_one (congrArg Subtype.val hn)
  have htop : N = ⊤ := hnormal.eq_bot_or_eq_top.resolve_left hne
  intro g hg
  have hn : (⟨g, hg⟩ : D) ∈ N := htop ▸ Subgroup.mem_top _
  exact hn

/-- The elementary and commutator conventions coincide at the four-dimensional endpoint. -/
theorem complement_elementary_eq_omega_rankOne (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (Minus.quadraticForm F 2) =
      Minus.Omega F (Minus.Space F 1) (Minus.quadraticForm F 2) :=
  le_antisymm (complement_elementary_le_omega 1 (by decide) h2)
    (rankOne_commutator_le_elementary h2)

end ClassicalOrthogonal.Fundamental.MinusCentralizer
