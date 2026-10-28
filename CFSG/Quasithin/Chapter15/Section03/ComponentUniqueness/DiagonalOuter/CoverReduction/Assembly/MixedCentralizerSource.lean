module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.SylowSource.Normalizer
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FixedFixerSource
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.AmbientSource
public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.SourceFusion

/-!
# The selected mixed centralizer and field coset

The selected graph and field involutions determine the actual normalizer
geometry. Fixed residuals transport through the original subgroup inclusions,
giving the odd core and extraspecial Sylow three-subgroup in the literal
ambient mixed centralizer. Diagonal movement also discharges the center-action
premise of field-coset fusion. These are the three inputs of the field terminal.
Source: Aschbacher–Smith, 15.3.38, printed pp.1136–1137.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel Matrix.PSL3Four.ExtendedCentralizer
variable {G : Type*} [Group G] [Finite G]

/-- Fixed points of relative conjugation are the literal ambient intersection. -/
def relativeFixedEquiv (I L : Subgroup G) (hLI : L ≤ I)
    [(L.subgroupOf I).Normal] (w : I) :
    (MulAut.conjNormal w : MulAut (L.subgroupOf I)).fixedSubgroup ≃*
      (L ⊓ centralizer ({(w : G)} : Set G) : Subgroup G) where
  toFun x := ⟨x.val.val.val, x.val.property, by
    apply mem_centralizer_singleton_iff.mpr
    have hx := congrArg (fun z : L.subgroupOf I => ((z : I) : G))
      ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    change (w : G) * (x.val.val : G) * (w : G)⁻¹ = (x.val.val : G) at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
  invFun x := ⟨⟨⟨x.val, hLI x.property.1⟩, x.property.1⟩, by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    apply Subtype.ext
    change (w : G) * (x : G) * (w : G)⁻¹ = (x : G)
    rw [← mem_centralizer_singleton_iff.mp x.property.2, mul_inv_cancel_right]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The intrinsic fixed residual transports through the original inclusions. -/
def relativeFixedResidualEquiv (I L : Subgroup G) (hLI : L ≤ I)
    [(L.subgroupOf I).Normal] (w : I) :
    pResidual 2 (MulAut.conjNormal w : MulAut (L.subgroupOf I)).fixedSubgroup ≃*
      pResidual 2 (L ⊓ centralizer ({(w : G)} : Set G) : Subgroup G) := by
  let e := relativeFixedEquiv I L hLI w
  exact (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_pResidual 2 e))

/-- The actual source mixed centralizer has odd core E₉ and an extraspecial
Sylow subgroup of order 27 and exponent three. -/
theorem source_mixed_centralizer {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r) :
    Nonempty (pPrimeCore 2 (I ⊓ centralizer
      ({(b.lift.dihedral.firstReflection : G) *
        (b.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃* ElementaryNine) ∧
    ∃ P : Sylow 3 (I ⊓ centralizer
      ({(b.lift.dihedral.firstReflection : G) *
        (b.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G),
      IsExtraspecial 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3 := by
  let : (L.subgroupOf I).Normal := r.cover.normal
  let : Fintype r.marking.F := Fintype.ofFinite _
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let f : r.marking.F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      r.marking.card, Matrix.PSL3Four.card_F])
  let e := Atlas.fieldEquivPSL 3 f
  obtain ⟨n, hnτ, hnf⟩ := source_selected_normalizer_geometry s h r b e
  have hw : (n.graphFieldI : G) = (b.lift.dihedral.firstReflection : G) *
      (b.lift.dihedral.halfTurn : G) := by
    change (n.tauI : G) * (n.fieldI : G) = _
    rw [hnτ, hnf]
  obtain ⟨eR⟩ := graphField_intersection_residual_model h r b.lift
  rw [← hw] at eR
  let eF := (relativeFixedResidualEquiv I L h.component_le n.graphFieldI).trans eR
  have hh := n.ambient_oddCore_and_sylow I (r.extendedOvergroup s h e) eF
  rw [hw] at hh
  exact hh

/-- The actual selected field coset is a single ambient conjugacy class. -/
theorem source_field_coset_conjugate {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r)
    (x : G) (hx : orderOf x = 2)
    (hxL : x * (b.lift.dihedral.halfTurn : G)⁻¹ ∈ L) :
    IsConj x (b.lift.dihedral.halfTurn : G) := by
  let : (L.subgroupOf I).Normal := r.cover.normal
  let : Fintype r.marking.F := Fintype.ofFinite _
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let f : r.marking.F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      r.marking.card, Matrix.PSL3Four.card_F])
  obtain ⟨n, _, hnf⟩ := source_selected_normalizer_geometry s h r b (Atlas.fieldEquivPSL 3 f)
  rw [← hnf] at hxL ⊢
  exact n.ambient_field_coset_conjugate I x hx (by
    exact ⟨⟨_, h.component_le hxL⟩, hxL, rfl⟩)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
