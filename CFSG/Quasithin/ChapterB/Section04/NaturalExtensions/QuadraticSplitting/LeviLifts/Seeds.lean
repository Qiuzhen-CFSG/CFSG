module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Coordinates
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Propagation

/-!
# The parabolic-fixed seed in B.4.9(1)

Exchange the marked quotient coordinate j with a different coordinate i.
The conjugate of the quadratic axis group has displacements onto the entire
quotient line F e_j. Each such displacement is fixed by that conjugate,
and hence by its intersection P with the literal Levi K.

This constructs the source's P-fixed lifts before any cohomology or splitting
argument, using only the original quotient map. Both quotient orientations
are allowed; the construction uses the quotient's actual actor marking.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(1), printed pp.92–93.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open Representation.OneCohomology.SLHigherNatural Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
open CFSG.Quasithin.ChapterB.NaturalExtensions
open CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ} (m : QuotientCoordinates d)
  {i j : Fin n} (hij : i ≠ j)

/-- The elementary three-factor word exchanging coordinates i and j. -/
noncomputable def exchangeActor : G :=
  m.action.groupEquiv.symm
    (transvection hij (1 : F.Carrier) * transvection hij.symm 1 * transvection hij 1)

/-- The source subgroup P: the intersection of K with the exchanged axis group. -/
noncomputable def seedGroup : Subgroup G :=
  m.K j ⊓ (m.Q j).map (MulAut.conj (exchangeActor m hij)).toMonoidHom

/-- The chosen exchange sends the i-coordinate line to the j-coordinate line. -/
theorem natural_exchange_single (a : F.Carrier) :
    linearNatural F n (m.action.groupEquiv (exchangeActor m hij)) (Pi.single i a) =
      Pi.single j a := by
  simp only [exchangeActor, MulEquiv.apply_symm_apply]
  change specialLinearNatural n (_ * _ * _) _ = _
  simp only [map_mul, Module.End.mul_apply]
  simp only [action_transvection, Pi.single_eq_of_ne hij.symm, mul_zero, Pi.single_zero,
    add_zero, Pi.single_eq_same, one_mul, Pi.add_apply]
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij, CharTwo.add_self_eq_zero]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm]
    · simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

/-- The elementary transvection with column j fixes the quotient axis pointwise. -/
theorem elementary_mem_Q (a : F.Carrier) :
    m.action.groupEquiv.symm (transvection hij a) ∈ m.Q j := by
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro z hz
  apply m.action.linearEquiv.injective
  rw [m.action.intertwines, MulEquiv.apply_symm_apply]
  change (m.action.linearEquiv z) j = 0 at hz
  change specialLinearNatural n (transvection hij a) (m.action.linearEquiv z) = _
  rw [action_transvection, hz, mul_zero, Pi.single_zero, add_zero]

/-- Every vector of the quotient line has an actual P-fixed lift. -/
theorem seed_fixed_lifts (hq : IsQuadratic ρ (m.Q j)) :
    m.line j ≤ (fixedSpace ρ (seedGroup m hij)).map d.space.toSubmodule.mkQ := by
  intro z hz
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
  have haz : m.action.linearEquiv z = Pi.single j a := by
    change a • Pi.single j 1 = m.action.linearEquiv z at ha
    rw [← ha]
    ext k
    by_cases hk : k = j <;> simp [hk]
  let t := m.action.groupEquiv.symm (transvection hij (1 : F.Carrier))
  have ht : t ∈ m.Q j := elementary_mem_Q m hij 1
  obtain ⟨w, hw⟩ := d.space.toSubmodule.mkQ_surjective
    (m.action.linearEquiv.symm (Pi.single j a))
  have hw' : m.action.linearEquiv (d.space.toSubmodule.mkQ w) = Pi.single j a := by
    rw [hw, LinearEquiv.apply_symm_apply]
  let g := exchangeActor m hij
  let v := ρ g (ρ t w - w)
  refine ⟨v, ?_, ?_⟩
  · intro b
    obtain ⟨c, hc, he⟩ := b.property.2
    change ρ b.val (ρ g (ρ t w - w)) = ρ g (ρ t w - w)
    rw [← he]
    change ρ (g * c * g⁻¹) (ρ g (ρ t w - w)) = _
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one, map_mul, Module.End.mul_apply]
    rw [hq c hc t ht w]
  · apply m.action.linearEquiv.injective
    change m.action.linearEquiv
      (d.space.quotientRepresentation g (d.space.toSubmodule.mkQ (ρ t w - w))) = _
    rw [m.action.intertwines, map_sub, map_sub]
    change linearNatural F n (m.action.groupEquiv g)
      (m.action.linearEquiv (d.space.quotientRepresentation t (d.space.toSubmodule.mkQ w)) -
        m.action.linearEquiv (d.space.toSubmodule.mkQ w)) = _
    rw [m.action.intertwines, hw']
    simp only [t, MulEquiv.apply_symm_apply]
    change linearNatural F n (m.action.groupEquiv g)
      (specialLinearNatural n (transvection hij 1) (Pi.single j a) - Pi.single j a) = _
    rw [action_transvection, Pi.single_eq_same, one_mul, add_sub_cancel_left]
    exact (natural_exchange_single m hij a).trans haz.symm

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
