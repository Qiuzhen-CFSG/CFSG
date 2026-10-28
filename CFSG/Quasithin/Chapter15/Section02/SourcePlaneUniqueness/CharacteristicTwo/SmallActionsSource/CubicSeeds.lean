module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Seeds
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.SylowIndexThree
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Intrinsic cubic quotients of the corrected source seeds

For an S-normalized two-perfect seed Y, adjoining the two-group S leaves
O²(YS)=Y. The actual S₃ quotient of YS then gives |Y/O₂(Y)|=3. These
statements apply to every source seed, including the arbitrary seed of
15.2.22. They do not identify it with O^{3′}(NI).

Source: Aschbacher--Smith 15.2.21(3)--22, printed p.1114.
The middle-parabolic consumer uses the intrinsic quotient for Y₀.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]
variable {M I S Y : Subgroup G}

omit [Finite G] in
/-- The corrected source seed is exactly the two-residual after adjoining S. -/
theorem Seed.join_residual (s : Seed M I S Y) (hS : IsPGroup 2 S) :
    (pResidual 2 (Y ⊔ S : Subgroup G)).map (Y ⊔ S).subtype = Y :=
  embedded_pResidual_join_pGroup Y S s.perfect hS s.normalized

/-- The first numerical inference in 15.2.21(3), for an arbitrary source seed. -/
theorem Seed.core_quotient_card (s : Seed M I S Y) (hS : IsPGroup 2 S) :
    Nat.card (Y ⧸ pCore 2 Y) = 3 := by
  let D := Y ⊔ S
  obtain ⟨e⟩ := s.quotient
  let P : Sylow 2 D := Sylow.nonempty.some
  have hc := residual_core_quotient_card_of_sylow_index_three P
    (SymmetricThreeTwoCore.sylow_index_three e P)
  let eY : pResidual 2 D ≃* Y :=
    ((pResidual 2 D).equivMapOfInjective D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr (s.join_residual hS))
  exact (Nat.card_congr (QuotientGroup.congr _ _ eY (pCore_map_iso 2 eY)).toEquiv).symm.trans hc
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
