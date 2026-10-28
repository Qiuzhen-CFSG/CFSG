module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit

/-!
# Local centralizers and involution fusion in Chapter J

This boundary exports the exact targets for J.2.4–6 and J.2.8, the proved
fusion of U minus the identity from J.2.1, and the omega/Frattini deduction
from the quaternion decomposition of HC. The three source branches are
assembled below from the explicit J.2.2(5) and J.2.3(7) inputs.

Source: Aschbacher–Smith, printed pp.434–435 and 437–438.
-/

public section
noncomputable section

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion

variable {G : Type*} [Group G] [Finite G]

/-- The complete J.2.4--6 and J.2.8 package from the two earlier conclusions
used by the source proof.  The first premise is the literal J.2.2(5)
conjugate-intersection conclusion, and the second is J.2.3(7) for the actual
`C_Q(B)`.  The quaternion decomposition is constructed once and shared by
the commutator, outer-involution and orbit arguments. -/
theorem source_conclusions_of_earlier
    (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (h225 : ∀ l : d.L,
      ConjugateIntersections.conjugateU d l ≠ d.toTypeRuSetup.U →
      Nat.card (((ConjugateIntersections.conjugateU d l).subgroupOf
        d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
      ConjugateIntersections.conjugateU d l ⊓ d.toTypeRuSetup.HC = d.V)
    (hq : Nonempty (HB d.toTypeRuSetup B ≃* QuaternionGroup 2))
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1) :
    SourceJ24 d.toTypeRuSetup ∧ SourceJ25 d.toTypeRuSetup B ∧
      SourceJ26 d.toTypeRuSetup z ∧ SourceJ28 d.toTypeRuSetup z := by
  let cp := centralProductData_of_quaternion d B hq
  have h24 := sourceJ24_of_quaternion d B hq
  have h25_26 := Outer.sourceJ25_sourceJ26_of_centralProduct d B cp hz hz1
  have h28 := CoreOrbit.sourceJ28_of_earlier_source d h225 h24 h25_26.2
  exact ⟨h24, h25_26.1, h25_26.2, h28⟩

end CFSG.Quasithin.ChapterJ.Fusion
