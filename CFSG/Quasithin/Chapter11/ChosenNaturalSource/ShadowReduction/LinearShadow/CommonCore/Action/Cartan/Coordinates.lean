module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.GeometryReductions

/-!
# Changing natural coordinates and excluding the fixed alternative

A basis change conjugates the actual K/O₂(K) marking and transports every
natural summand by the same matrix. Thus a conjugate diagonal suffices for
the existing fixed-space consumer. If the L-module calculation gives the
comparison-or-centralization alternative, the original hypothesis [Z,H]≠1
excludes centralization. The Hall diagonal and L-module alternative remain
explicit source obligations; this is not the completed source 11.3.7.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(3), printed p.773.
-/

open Subgroup Theory.GroupTheory Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] {T : Sylow 2 G} {H : Subgroup G} {F : BinaryField}
namespace NaturalQuotientMarking
variable (c : NaturalQuotientMarking T H F)
def changeBasis (b : SpecialLinearGroup (Fin 2) F.Carrier) : NaturalQuotientMarking T H F where
  multiplicity := c.multiplicity
  positive := c.positive
  quotientEquiv := c.quotientEquiv.trans (MulAut.conj b)
  coordinates := (AddEquiv.piCongrRight (fun _ : Fin c.multiplicity =>
    (SpecialLinearGroup.toLin' b).toAddEquiv)).toMultiplicative.toMonoidHom.comp c.coordinates
  surjective := (AddEquiv.piCongrRight (fun _ : Fin c.multiplicity =>
    (SpecialLinearGroup.toLin' b).toAddEquiv)).toMultiplicative.surjective.comp c.surjective
  kernel := by
    apply Eq.trans _ c.kernel
    exact MonoidHom.ker_comp_of_injective c.coordinates
      (AddEquiv.piCongrRight (fun _ : Fin c.multiplicity =>
        (SpecialLinearGroup.toLin' b).toAddEquiv)).toMultiplicative.toMonoidHom
      (MulEquiv.injective _)
  intertwines := by
    intro k v i
    change b.val *ᵥ (c.coordinates (residualAction T H k v)).toAdd i =
      (b * c.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val *ᵥ
        (b.val *ᵥ (c.coordinates v).toAdd i)
    rw [c.intertwines]
    rw [mulVec_mulVec, mulVec_mulVec]
    have he : (b * c.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹) * b =
        b * c.quotientEquiv (QuotientGroup.mk' _ k) := by group
    exact congrArg (fun x : SpecialLinearGroup (Fin 2) F.Carrier =>
      x.val *ᵥ (c.coordinates v).toAdd i) he.symm

/-- The new quotient marking and all natural copies use the same basis change. -/
theorem changeBasis_coordinates (b : SpecialLinearGroup (Fin 2) F.Carrier)
    (v : omegaClosure T H) (i : Fin c.multiplicity) :
    ((c.changeBasis b).coordinates v).toAdd i = b.val *ᵥ (c.coordinates v).toAdd i := rfl

/-- A conjugate split element suffices; the initial marking need not diagonalize it. -/
theorem omega_fixed_eq_of_conjugate_diagonal
    (B : Subgroup G) (hBK : B ≤ outsideResidual H)
    (d : outsideResidual H) (hd : (d : G) ∈ B)
    (b : SpecialLinearGroup (Fin 2) F.Carrier)
    (a : F.Carrier) (ha : a ≠ 1)
    (hdiag : (b * c.quotientEquiv (QuotientGroup.mk' _ d) * b⁻¹).val = !![a,0;0,a⁻¹]) :
    omegaCenter T ⊓ centralizer (B : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G) :=
  (c.changeBasis b).omega_fixed_eq_of_diagonal B hBK d hd a ha hdiag
end NaturalQuotientMarking

variable [Finite G] {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The moving source Z cannot centralize a subgroup with the K-fixed space. -/
theorem source_movement_of_common_fixed (s : Hypothesis1131At D S U₁ H)
    (B : Subgroup G)
    (he : omegaCenter T ⊓ centralizer (B : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G)) :
    ⁅omegaCenter T, B⁆ ≠ ⊥ := by
  intro hc
  have hZB : omegaCenter T ≤ centralizer (B : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hc
  have hZK : omegaCenter T ≤ centralizer (outsideResidual H : Set G) := by
    intro z hz
    exact (he.le ⟨hz,hZB hz⟩).2
  apply s.moves_omega_center
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  rw [← outsideResidual_sup_sylow T H s.outside.1.1.2]
  exact sup_le (le_centralizer_iff.mp hZK)
    (le_centralizer_iff.mp (omegaCenter_le_sylow_centralizer T))

/-- The source module dichotomy is resolved by the actual natural K-action. -/
theorem source_comparison_of_conjugate_diagonal
    (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (d : outsideResidual H) (hd : (d : G) ∈ oddCartanPart A)
    (b : SpecialLinearGroup (Fin 2) S.field.Carrier)
    (a : S.field.Carrier) (ha : a ≠ 1)
    (hdiag : (b * c.quotientEquiv (QuotientGroup.mk' _ d) * b⁻¹).val = !![a,0;0,a⁻¹])
    (hcases : omegaCenter T ⊓ centralizer (oddCartanPart A : Set G) =
        omegaCenter T ⊓ centralizer (L : Set G) ∨
      ⁅omegaCenter T, oddCartanPart A⁆ = ⊥) :
    omegaCenter T ⊓ centralizer (oddCartanPart A : Set G) =
      omegaCenter T ⊓ centralizer (L : Set G) := by
  have he := c.omega_fixed_eq_of_conjugate_diagonal _
    (oddCartanPart_le_residual_of_hall _ A hA hHall) d hd b a ha hdiag
  exact hcases.resolve_right (source_movement_of_common_fixed s _ he)

/-- Application to the existing fixed-space consumer, with coordinate transport
and the movement argument discharged. The Hall and L-module producers supply
only the displayed conjugate diagonal and dichotomy. -/
theorem source_fixed_spaces_of_cartan_dichotomy
    (s : Hypothesis1131At D S U₁ H)
    (hWT : omegaClosure T H ≤ (T : Subgroup G))
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (d : outsideResidual H) (hd : (d : G) ∈ oddCartanPart A)
    (b : SpecialLinearGroup (Fin 2) S.field.Carrier)
    (a : S.field.Carrier) (ha : a ≠ 1)
    (hdiag : (b * c.quotientEquiv (QuotientGroup.mk' _ d) * b⁻¹).val = !![a,0;0,a⁻¹])
    (hcases : omegaCenter T ⊓ centralizer (oddCartanPart A : Set G) =
        omegaCenter T ⊓ centralizer (L : Set G) ∨
      ⁅omegaCenter T, oddCartanPart A⁆ = ⊥) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧
      omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ :=
  source_fixed_spaces_of_diagonal s hWT (c.changeBasis b) A hA hHall d hd a ha hdiag
    (source_comparison_of_conjugate_diagonal s c A hA hHall d hd b a ha hdiag hcases)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
