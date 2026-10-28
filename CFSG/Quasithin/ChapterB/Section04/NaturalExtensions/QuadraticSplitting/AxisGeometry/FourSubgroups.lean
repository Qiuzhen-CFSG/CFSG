module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry

/-!
# Four-subgroups inside the marked axis group

Every nontrivial subgroup of the shear group fixes exactly the coordinate
axis, whose binary codimension is the defining-field degree. Consequently,
every subgroup of order four in Q is an elementary abelian common-axis
four-group in the precise sense of B.4.9(1). Over F₄ this discharges the
geometric clause in `AvailableFour`; root exclusion remains a separate
condition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed p.92, including the exceptional F₄ family.
-/

public section

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace QuotientCoordinates
variable (m : QuotientCoordinates d) (j : Fin n)

theorem Q_card : Nat.card (m.Q j) = 2 ^ (F.degree * (n - 1)) := by
  rw [Nat.card_congr (m.axisGroupEquiv j).toEquiv, hyperplaneCentralizer_card]

theorem axis_codim :
    Module.finrank (ZMod 2) ((V ⧸ d.space.toSubmodule) ⧸ m.axis j) = F.degree := by
  let ev : (V ⧸ d.space.toSubmodule) →ₗ[ZMod 2] F.Carrier :=
    ((LinearMap.proj j : (Fin n → F.Carrier) →ₗ[F.Carrier] F.Carrier).restrictScalars
      (ZMod 2)).comp m.action.linearEquiv.toLinearMap
  have hs : Function.Surjective ev := by
    intro c
    refine ⟨m.action.linearEquiv.symm (Pi.single j c), ?_⟩
    change m.action.linearEquiv (m.action.linearEquiv.symm (Pi.single j c)) j = c
    rw [LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  exact (LinearMap.quotKerEquivOfSurjective ev hs).finrank_eq.trans (field_finrank F)

theorem fixedSpace_subgroup_Q (A : Subgroup G) (hA : A ≤ m.Q j) (hne : A ≠ ⊥) :
    fixedSpace d.space.quotientRepresentation A = m.axis j := by
  apply le_antisymm
  · intro z hz
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨w, hw⟩ := m.exists_axisShear j ⟨a, hA ha⟩
    change m.axisShear j w = a at hw
    have hw0 : w ≠ 0 := by
      intro hw0
      apply ha1
      apply Subtype.ext
      change a = 1
      rw [← hw, hw0, m.axisShear_zero]
    have he := congrArg m.action.linearEquiv (hz ⟨a, ha⟩)
    change m.action.linearEquiv (d.space.quotientRepresentation a z) =
      m.action.linearEquiv z at he
    rw [← hw, m.axisShear_apply] at he
    have hzero : m.action.linearEquiv z j • w.val = 0 :=
      add_left_cancel (he.trans (add_zero _).symm)
    rcases smul_eq_zero.mp hzero with hc | hwz
    · exact hc
    · exact False.elim (hw0 (Subtype.ext hwz))
  · intro z hz a
    exact (hA a.property).2 z hz

theorem subgroup_Q_elementary (hn : 2 ≤ n) (A : Subgroup G) (hA : A ≤ m.Q j) :
    IsElementaryAbelian 2 A := by
  let f := (m.axisGroupEquiv j).toMonoidHom.comp (Subgroup.inclusion hA)
  have hf : Function.Injective f :=
    (m.axisGroupEquiv j).injective.comp (Subgroup.inclusion_injective hA)
  let := (hyperplaneCentralizer_elementary F n j hn).2
  refine {
    toIsMulCommutative := ⟨⟨fun a b => hf (by simp only [map_mul, mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro a
  apply hf
  rw [map_pow, map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (hyperplaneCentralizer F n j)) (f a)

/-- Every order-four subgroup of the marked Q satisfies the literal common-axis
condition. This constructs the geometric clause of the F₄ alternative. -/
theorem isAxisFour_of_le_Q (hn : 2 ≤ n) (A : Subgroup G)
    (hA : A ≤ m.Q j) (hcard : Nat.card A = 4) : IsAxisFour d A := by
  refine ⟨m.subgroup_Q_elementary j hn A hA, hcard, m.axis j, m.axis_codim j, ?_⟩
  intro e he he1
  apply m.fixedSpace_subgroup_Q j (Subgroup.zpowers e)
  · exact Subgroup.zpowers_le.mpr (hA he)
  · intro hz
    have hm := Subgroup.mem_zpowers e
    rw [hz, Subgroup.mem_bot] at hm
    exact he1 hm


/-- The F₄ family uses actual four-subgroups of Q. The common-axis condition
is proved here, while the source's genuine root exclusion remains explicit. -/
theorem availableFour_of_le_Q (hn : 2 ≤ n) (hF : F.degree = 2)
    (E A : Subgroup G) (hA : A ≤ m.Q j) (hcard : Nat.card A = 4)
    (hroot : ¬ InRootGroup d A) : AvailableFour d E A :=
  Or.inr ⟨hF, m.isAxisFour_of_le_Q j hn A hA hcard, hroot⟩

/-- Application to the original universal F₄ quadraticity assumption. -/
theorem quadratic_four_of_le_Q (h : SourceHypotheses d) (hF : F.degree = 2)
    (A : Subgroup G) (hA : A ≤ m.Q j) (hcard : Nat.card A = 4)
    (hroot : ¬ InRootGroup d A) : IsQuadratic ρ A := by
  have hn : 2 ≤ n := by
    rcases h.family with hn | ⟨_, hn⟩ <;> omega
  exact h.fourField hF A (m.isAxisFour_of_le_Q j hn A hA hcard) hroot

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
