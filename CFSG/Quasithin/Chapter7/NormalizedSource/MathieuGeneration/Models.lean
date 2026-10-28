module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.CentralCover
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M12
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M22
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M23
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24

/-!
# Mathieu Cartan restrictions and their central-cover consumers

The four native model calculations apply to every automorphism subgroup
containing the inner automorphisms. Faithful descent transfers these bounds
to all perfect central covers. The final theorem discharges exactly the
`MathieuCartanRestriction` contract used by the quotient-conjugation consumer.

Source: Aschbacher--Smith, Table 7.2.1 and 7.3.4, printed pp.698--699.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterE.Section06.FixedPointBounds
universe u

/-- The literal Cartan bound for every perfect central cover of M₁₂. -/
theorem m12_centralCover_cartanRestriction
    {X : Type u} [Group X] [Finite X] [Group.IsPerfect X]
    (e : (X ⧸ center X) ≃* Sporadic.Mathieu.M12)
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ 2 :=
  cartan_restriction_of_centralQuotient e Models.m12_cartanRestriction A hA

/-- The literal Cartan bound for every perfect central cover of M₂₂,
including the triple cover occurring in the source table. -/
theorem m22_centralCover_cartanRestriction
    {X : Type u} [Group X] [Finite X] [Group.IsPerfect X]
    (e : (X ⧸ center X) ≃* Sporadic.Mathieu.M22)
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ 2 :=
  cartan_restriction_of_centralQuotient e Models.m22_cartanRestriction A hA

/-- The literal Cartan bound for every perfect central cover of M₂₃. -/
theorem m23_centralCover_cartanRestriction
    {X : Type u} [Group X] [Finite X] [Group.IsPerfect X]
    (e : (X ⧸ center X) ≃* Sporadic.Mathieu.M23)
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ 2 :=
  cartan_restriction_of_centralQuotient e Models.m23_cartanRestriction A hA

/-- The literal Cartan bound for every perfect central cover of M₂₄. -/
theorem m24_centralCover_cartanRestriction
    {X : Type u} [Group X] [Finite X] [Group.IsPerfect X]
    (e : (X ⧸ center X) ≃* Sporadic.Mathieu.M24)
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ 2 :=
  cartan_restriction_of_centralQuotient e Models.m24_cartanRestriction A hA

/-- Alternative assembly accepting an explicit M₂₃ calculation. The other
three model inputs and all central-cover transports are discharged here. -/
theorem mathieuCartanRestriction_of_m23
    (h23 : ∀ A : Subgroup (MulAut Sporadic.Mathieu.M23),
      MulAut.innerSubgroup Sporadic.Mathieu.M23 ≤ A → nPrime A ≤ 2) :
    MathieuCartanRestriction.{u} :=
  mathieuCartanRestriction_of_models Models.m12_cartanRestriction
    Models.m22_cartanRestriction h23 Models.m24_cartanRestriction

/-- Alternative assembly accepting explicit M₂₃ and M₂₄ calculations. -/
theorem mathieuCartanRestriction_of_m23_m24
    (h23 : ∀ A : Subgroup (MulAut Sporadic.Mathieu.M23),
      MulAut.innerSubgroup Sporadic.Mathieu.M23 ≤ A → nPrime A ≤ 2)
    (h24 : ∀ A : Subgroup (MulAut Sporadic.Mathieu.M24),
      MulAut.innerSubgroup Sporadic.Mathieu.M24 ≤ A → nPrime A ≤ 2) :
    MathieuCartanRestriction.{u} :=
  mathieuCartanRestriction_of_models Models.m12_cartanRestriction
    Models.m22_cartanRestriction h23 h24

/-- The complete Mathieu Cartan restriction, retaining every quasisimple
central cover and every inner-containing automorphism subgroup. -/
theorem mathieuCartanRestriction : MathieuCartanRestriction.{u} :=
  mathieuCartanRestriction_of_models Models.m12_cartanRestriction
    Models.m22_cartanRestriction Models.m23_cartanRestriction Models.m24_cartanRestriction

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
