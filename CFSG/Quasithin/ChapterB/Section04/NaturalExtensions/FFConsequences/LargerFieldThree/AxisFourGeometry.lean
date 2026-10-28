module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.Reduction
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.FullAxis
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.AxisFourGeometry.Conjugacy
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.AxisFourGeometry.StandardFour
/-!
# Source four-groups from the quadratic full axis actor

A determinant-one change of quotient coordinates places the full axis actor
in the coordinate hyperplane centralizer. The binary plane of two independent
shears pulls back to a four-group inside the original actor. Its common fixed
space is on the literal quotient, and its two displacement directions exclude
root containment under the original natural marking.

All hyperplane centralizers are conjugate in SL₃. Consequently quadraticity
of the given full axis actor makes every source axis four-group quadratic,
including those on different axes. This discharges the global F₄ clause and
constructs all of QuadraticSplitting.SourceHypotheses without a splitting
assumption. The final application uses the actual Thompson replacement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(1)–(2), printed pp.92–94.
-/

public section
open Representation Representation.BinaryOffender Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree.AxisFourGeometry
open QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V} (d : DoubleNatural F 3 ρ)

/-- Transport the coordinate common axis to the literal quotient by d.space. -/
theorem axis_four_of_marked_standard
    (m : ActionEquiv d.space.quotientRepresentation (linearNatural F 3))
    {E : Subgroup G} (he : IsElementaryAbelian 2 E) (hc : Nat.card E = 4)
    (hE : E.map m.groupEquiv.toMonoidHom ≤ hyperplaneCentralizer F 3 0) :
    IsAxisFour d E := by
  have hne : E ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_fintype_card] at hc
    norm_num at hc
  have hne' : E.map m.groupEquiv.toMonoidHom ≠ ⊥ :=
    fun h => hne ((E.map_eq_bot_iff_of_injective m.groupEquiv.injective).mp h)
  have hfixed := subgroup_fixedSpace F 3 0 hE hne'
  refine ⟨he, hc, fixedSpace d.space.quotientRepresentation E, ?_, ?_⟩
  · change fixedCodim d.space.quotientRepresentation E = F.degree
    rw [fixedCodim_map_equivariant _ (linearNatural F 3) m.groupEquiv.toMonoidHom
      m.linearEquiv m.intertwines]
    exact subgroup_fixedCodim F 3 0 hE hne'
  · intro a ha hane
    apply Submodule.map_injective_of_injective (f := m.linearEquiv.toLinearMap) m.linearEquiv.injective
    rw [fixedSpace_map_equivariant _ (linearNatural F 3) m.groupEquiv.toMonoidHom
      m.linearEquiv m.intertwines,
      fixedSpace_map_equivariant _ (linearNatural F 3) m.groupEquiv.toMonoidHom
      m.linearEquiv m.intertwines, hfixed]
    apply subgroup_fixedSpace F 3 0
    · exact (Subgroup.map_mono (Subgroup.zpowers_le.mpr ha)).trans hE
    · intro h
      have ha' : m.groupEquiv a ∈ (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F.Carrier)) :=
        h ▸ Subgroup.mem_map_of_mem m.groupEquiv.toMonoidHom (Subgroup.mem_zpowers a)
      exact hane (m.groupEquiv.injective ((Subgroup.mem_bot.mp ha').trans m.groupEquiv.map_one.symm))

private noncomputable def conjugatedAction
    (m : ActionEquiv d.space.quotientRepresentation (linearNatural F 3))
    (s : SpecialLinearGroup (Fin 3) F.Carrier) :
    ActionEquiv d.space.quotientRepresentation (linearNatural F 3) where
  groupEquiv := m.groupEquiv.trans (MulAut.conj s)
  linearEquiv := m.linearEquiv.trans (s.toLin'.restrictScalars (ZMod 2))
  intertwines g v := by
    change linearNatural F 3 s (m.linearEquiv (d.space.quotientRepresentation g v)) =
      linearNatural F 3 (s * m.groupEquiv g * s⁻¹) (linearNatural F 3 s (m.linearEquiv v))
    rw [m.intertwines, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      inv_self_apply]

/-- A full axis actor contains a literal elementary four with two independent
shear directions, hence with no root-group containment in the original marking. -/
theorem exists_axis_four_in_full_axis
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {B : Subgroup G}
    (hB : IsFullAxisGroup F 3 (B.map (d.threeQuotientAction e).groupEquiv.toMonoidHom)) :
    ∃ E : Subgroup G, E ≤ B ∧ IsAxisFour d E ∧ ¬ InRootGroup d E := by
  let m₀ := d.threeQuotientAction e
  obtain ⟨s, hs⟩ := full_axis_conjugate_standard F hB
  let m := conjugatedAction d m₀ s
  have hmB : B.map m.groupEquiv.toMonoidHom = hyperplaneCentralizer F 3 0 := by
    rw [Subgroup.map_map] at hs
    exact hs
  let E := (standardFour F).map m.groupEquiv.symm.toMonoidHom
  have hmE : E.map m.groupEquiv.toMonoidHom = standardFour F := by
    change ((standardFour F).map m.groupEquiv.symm.toMonoidHom).map
      m.groupEquiv.toMonoidHom = _
    rw [Subgroup.map_map]
    have hf : m.groupEquiv.toMonoidHom.comp m.groupEquiv.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro g
      exact m.groupEquiv.apply_symm_apply g
    rw [hf, Subgroup.map_id]
  have hEB : E ≤ B := by
    intro a ha
    have hm : m.groupEquiv a ∈ B.map m.groupEquiv.toMonoidHom := by
      rw [hmB]
      exact standardFour_le F (hmE ▸ Subgroup.mem_map_of_mem _ ha)
    obtain ⟨b, hb, hba⟩ := hm
    exact m.groupEquiv.injective hba ▸ hb
  have he : IsElementaryAbelian 2 E := by
    let := standardFour_elementary F
    exact IsElementaryAbelian.map m.groupEquiv.symm.toMonoidHom
  have hc : Nat.card E = 4 := by
    change Nat.card ((standardFour F).map m.groupEquiv.symm.toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective m.groupEquiv.symm.injective, standardFour_card]
  refine ⟨E, hEB, axis_four_of_marked_standard d m he hc ?_, ?_⟩
  · rw [hmE]
    exact standardFour_le F
  · rintro ⟨r, i, j, hij, hroot⟩
    apply standardFour_not_root F
    refine ⟨s * r, i, j, hij, ?_⟩
    intro a ha
    rw [← hmE] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨c, hc⟩ := hroot b hb
    refine ⟨c, ?_⟩
    change s * d.natural.groupEquiv b * s⁻¹ = _
    rw [hc]
    group

end CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree.AxisFourGeometry

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural
open QuasisimpleSource LargerFieldThree.AxisFourGeometry
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V} (d : DoubleNatural F 3 ρ)

/-- The full quadratic axis replacement supplies every hypothesis of B.4.9(1),
including the universal four-group clause over F₄. -/
theorem three_sourceHypotheses_of_full_axis
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {B : Subgroup G} (hq : IsQuadratic ρ B)
    (hB : IsFullAxisGroup F 3 (B.map (d.threeQuotientAction e).groupEquiv.toMonoidHom)) :
    QuadraticSplitting.SourceHypotheses d := by
  obtain ⟨E, hEB, hE, hroot⟩ := exists_axis_four_in_full_axis d e hB
  refine ⟨Or.inl rfl, ⟨E, hE, ?_, fun _ => hroot⟩, ?_⟩
  · exact fun a ha b hb v => hq a (hEB ha) b (hEB hb) v
  · intro _ A hA _
    exact axis_four_quadratic F d e hq hB hA

/-- Literal application to the marked replacement already supplied by the
larger-field FF reduction. No extra geometric premise remains. -/
theorem three_sourceHypotheses_of_bestOffender [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsBestOffender ρ A) : QuadraticSplitting.SourceHypotheses d := by
  obtain ⟨e, B, _, _, hq, _, _, hB⟩ := d.three_full_axis_replacement hA
  exact d.three_sourceHypotheses_of_full_axis e hq hB

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural
