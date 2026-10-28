module

public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.Frattini.PGroup

/-!
# The genuine triality parabolic cores at q = 2

The intrinsic two-core of a full parabolic is equivalent to its actual root
radical. For the arms node at q=2, the center has order two and equals the
Frattini subgroup; the radical has order 512. Its Frattini quotient is therefore
elementary abelian and nontrivial, giving extraspeciality.

The parameter remains symbolic until the field-order equality is used, avoiding
expensive reduction of the concrete graph-field carrier. The consumer transports
this core onto the original parabolic in Aschbacher--Smith 14.2.16, printed p.986.
The root calculations are those of F.1.12(I)(4), printed pp.263--264.
-/

@[expose] public noncomputable section

namespace Triality.Standard.Parabolics
open Subgroup

/-- The intrinsic two-core of the full parabolic is the actual root radical. -/
def parabolicTwoCoreEquivRadical (P : Parameters) (hp : P.prime = 2) (a : Node) :
    pCore 2 (parabolic P a) ≃* radical P a :=
  ((pCore 2 (parabolic P a)).equivMapOfInjective
    (parabolic P a).subtype (parabolic P a).subtype_injective).trans
      (MulEquiv.subgroupCongr (parabolic_twoCore_map P hp a))

/-- The first radical at q=2 is extraspecial, with its actual Frattini quotient. -/
theorem arms_radical_extraspecial_at_two (P : Parameters) (hp : P.prime = 2)
    (hq : P.q = 2) : IsExtraspecial 2 (radical P .arms) := by
  let Q := radical P .arms
  have hc : Nat.card (center Q) = 2 :=
    (RadicalCoordinates.card_center_radical_arms P hp).trans hq
  have hQ : Nat.card Q = 512 := by
    rw [RadicalCoordinates.radical_arms_card P hp, hq]
    norm_num
  let : Fact (IsPGroup 2 Q) := ⟨RadicalCoordinates.radical_isPGroup P hp .arms⟩
  refine ⟨hc, ?_, QuotientGroup.nontrivial_iff.mpr ?_⟩
  · let : IsElementaryAbelian 2 (Q ⧸ frattini Q) := isElementaryAbelian_quotient_frattini
    let a := QuotientGroup.quotientMulEquivOfEq
      (RadicalCoordinates.center_radical_arms_eq_frattini P hp).symm
    exact IsElementaryAbelian.of_surjective a.toMonoidHom a.surjective
  · intro he
    rw [he, card_top, hQ] at hc
    contradiction

end Triality.Standard.Parabolics
