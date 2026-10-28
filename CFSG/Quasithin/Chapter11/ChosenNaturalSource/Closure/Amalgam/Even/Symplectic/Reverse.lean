module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Alignment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.SmallCommutator
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Setup

/-!
# A single reverse-line obligation for both even symplectic alternatives

Pulling the common commutator back by the inverse conjugator gives the
displacement of an elementary subgroup on the original V. It normalizes V
by the literal mutual-commutator bound, and its displacement has exactly q
elements. Thus both alternatives use the same small-displacement field-line
criterion. In the plane alternative the actor is V₃ pulled back, not V.

The small-displacement criterion is proved from the actual semilinear
normalizer action, including q=4. Its application below retains the literal
quotient and the field structure on both modules. Source: Aschbacher--Smith 11.5.8, printed p.784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
open Closure.Symplectic LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

/-- The small-displacement criterion on the literal original module. -/
@[expose] def SmallCommutatorLines : Prop :=
  V ⊓ centralizer (L : Set G) = ⊥ →
  ∀ A : Subgroup G, IsElementaryAbelian 2 A →
    A ≤ normalizer (V : Set G) → Nat.card (⁅V,A⁆ : Subgroup G) = 2 ^ E.input.field.degree →
    IsFieldLine E (.sp4 m.action) ⁅V,A⁆

/-- The actual normalizer action proves the small-displacement criterion.
In particular this hypothesis in the transport lemmas is now discharged. -/
theorem smallCommutatorLines : SmallCommutatorLines E m := by
  intro hc A hA hn hcard
  let := hA
  have hne : ⁅A,V⁆ ≠ ⊥ := by
    intro hz
    rw [commutator_comm, hz] at hcard
    have hF : 1 < Nat.card E.input.field.Carrier := by
      let := Fintype.ofFinite E.input.field.Carrier
      simpa only [Nat.card_eq_fintype_card] using
        (Fintype.one_lt_card (α := E.input.field.Carrier))
    rw [E.input.field.card_eq] at hF
    have hb : Nat.card (⊥ : Subgroup G) = 1 := by simp
    rw [hb] at hcard
    omega
  have hbound : Nat.card (⁅A,V⁆ : Subgroup G) ≤ Nat.card E.input.field.Carrier := by
    rw [commutator_comm, hcard, E.input.field.card_eq]
  rw [commutator_comm]
  exact commutator_isFieldLine_of_card_le m.action hc A hn
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A)) hne hbound

include m in
/-- The original distinguished point has q elements when C_V(L)=1. -/
theorem card_point (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card E.V₁ = 2 ^ E.input.field.degree := by
  rw [m.point_preimage]
  change Nat.card ((Coordinates.sp4 m.action).preimage (m.flag.space 0)) = _
  rw [Nonabelian.card_preimage _ hc, m.flag.dimension]
  simp

/-- Pull back the actual common commutator, with its exact normalizer and
cardinality hypotheses, to apply the independent small-displacement theorem. -/
theorem reverse_line_of_commutator
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hsmall : SmallCommutatorLines E m)
    (g : G) (A : Subgroup G) (hAV : A ≤ V)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (he : ⁅A,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₁) :
    IsFieldLine E (.sp4 m.action) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom) := by
  let A' := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hback : ⁅V,A'⁆ = E.V₁.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hh := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) he
    rw [map_commutator,map_conj_cancel,commutator_comm] at hh
    exact hh
  have hnorm : A' ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hh : ⁅A,V.map (MulAut.conj g).toMonoidHom⁆ ≤
        V.map (MulAut.conj g).toMonoidHom :=
      (commutator_mono hAV le_rfl).trans (hi.trans inf_le_right)
    have hh' := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
    rw [map_commutator,map_conj_cancel] at hh'
    exact hh'
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAV
  have hel : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hcard : Nat.card (⁅V,A'⁆ : Subgroup G) = 2 ^ E.input.field.degree := by
    rw [hback,card_map_of_injective (MulAut.conj g⁻¹).injective,card_point E m hc]
  rw [← hback]
  exact hsmall hc A' hel hnorm hcard

/-- In either source alternative the same subgroup is a field line on the
conjugate module. The second branch uses the actual hyperplane V₃. -/
theorem reverse_line_of_alternatives
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hsmall : SmallCommutatorLines E m)
    (g : G)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (halt : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₁ ∨
      (⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₂ ∧
        ⁅E.V₃,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₁)) :
    IsFieldLine E (.sp4 m.action) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom) := by
  rcases halt with h | h
  · exact reverse_line_of_commutator E m hc hsmall g V le_rfl hi h
  · exact reverse_line_of_commutator E m hc hsmall g E.V₃
      (D.centralQuotientPreimage_le E.threeSpace) hi h.2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
