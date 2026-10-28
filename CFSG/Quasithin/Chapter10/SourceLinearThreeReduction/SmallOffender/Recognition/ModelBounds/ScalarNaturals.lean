module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Scalar
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts
public import Theory.Representation.BinaryDoubledNaturalCentralizer
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# Crossed centralization for the two natural source rows

The opposite perfect component acts through the scalar commutant on the
marked natural quotient, so it fixes that quotient. Full commutator
generation then gives crossed centralization on the original moved factor.
These applications remove the separate crossed premise for both natural
rows in the small-offender selector.
Source: Aschbacher--Smith 10.1.1(1),(3) and 10.2.12, pp.741,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem rank_one_crossed_of_marking
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  obtain ⟨n,hn,e,⟨c⟩⟩ := hrow
  let : NeZero n := ⟨by omega⟩
  let : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
  exact crossed_of_scalar_commutant D SL2.BinarySmall.natural e c
    (fun f hf => SL2NaturalOffenders.centralizer_scalar f.toAddMonoidHom hf) ht htn

theorem binary_three_crossed_of_marking
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : BinaryThreeNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  obtain ⟨e,⟨c⟩⟩ := hrow
  exact crossed_of_scalar_commutant D (specialLinearNatural 3) e c
    (fun f hf => BinaryDoubledNatural.natural_centralizer_scalar (by decide : 2 ≤ 3)
      f.toAddMonoidHom hf) ht htn

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
