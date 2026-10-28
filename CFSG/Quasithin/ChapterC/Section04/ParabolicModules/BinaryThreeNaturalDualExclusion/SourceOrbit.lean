module
public import CFSG.Quasithin.ChapterC.Section04.ParabolicModules.BinaryThreeNaturalDualExclusion
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoordinates

/-!
# The repeated-natural C.4.8 exclusion on the original chosen orbit

Restrict the original natural-dual coordinates to a C.2.8 actor still covering
their quotient, and apply the exclusion with the literal relative radical.
For the original actor itself, the marked binary-three seed supplies the
coordinates without an added coordinate premise. C.2.8 supplies normality of
the radical in the actor-radical join. Strict containment is unnecessary for
this module obstruction; it belongs to the classification producing the row.

These conditional applications discharge the repeated-natural branch of
C.4.8(2), not C.4.8 itself. Construction of the equivariant model bridge, the
C.2.8 input (and covering premise for a smaller actor), and exclusion of the
orthogonal row remain with their source assembly owners.
Source: Aschbacher--Smith C.2.8 and C.4.8(2), pp.147,153--154;
4.4.3(i.a) and 7.6--7.7, pp.619,702--709, refs/quasithin.pdf.
-/

public noncomputable section
open Representation Subgroup BinaryLinear.OuterCyclic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource ChapterB.QuasisimpleSource
open ChapterC.Section04.BinaryThreeNaturalDualExclusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Apply the exclusion to the literal C.2.8 actor B on D.sourceOrbit.
The original q and E are retained, and the explicit covering premise says that
B still surjects under this same q. C.2.8 proves relative normality of R in BR;
no ambient normality or identification of the two quotient markings is assumed. -/
theorem sourceOrbit_c28_no_repeated_natural_marking
    (b : ModelBridge) {H M B R : Subgroup G}
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R D.sourceOrbit)
    (hBL : B ≤ L)
    (q : L →* BinaryLinearThree.Group)
    (hqB : Function.Surjective (q.comp (inclusion hBL)))
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (hE : ∀ l v, E (doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l v) =
        BinaryLinearThree.NaturalDual.action (q l) (E v)) :
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy B M).trans hc.span_normalizes_radical)
    ∀ (d : ℕ), d = 3 ∨ d = 4 →
    ∀ (a : ((B ⊔ R : Subgroup G) ⧸ R.subgroupOf (B ⊔ R)) ≃* LinearGroup d)
      (m : ℕ), 0 < m →
      ∀ N : Additive D.sourceOrbit ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d),
        (∀ l v, N (doubledSeedAction B D.sourceOrbit
          (hBL.trans D.sourceOrbit_component_normalizes) l v) =
            fun i => a (radicalQuotientMap B R l) (N v i)) → False := by
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy B M).trans hc.span_normalizes_radical)
  dsimp only
  intro d hdims a m hm N hN
  apply no_radical_quotient_natural_marking B R D.sourceOrbit b
    (hBL.trans D.sourceOrbit_component_normalizes) (q.comp (inclusion hBL)) hqB E
    (fun l v => hE (inclusion hBL l) v) d hdims a m hm N hN

/-- For C.2.8 with the original actor L, the checked chosen-seed theorem
constructs q and E. Only the model bridge and the genuine C.2.8 input remain
explicit; the theorem excludes either repeated-natural row on the whole orbit. -/
theorem sourceOrbit_binary_c28_no_repeated_natural
    (b : ModelBridge)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {H M R : Subgroup G}
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R D.sourceOrbit) :
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy L M).trans hc.span_normalizes_radical)
    ∀ (d : ℕ), d = 3 ∨ d = 4 →
    ∀ (a : ((L ⊔ R : Subgroup G) ⧸ R.subgroupOf (L ⊔ R)) ≃* LinearGroup d)
      (m : ℕ), 0 < m →
      ∀ N : Additive D.sourceOrbit ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d),
        (∀ l v, N (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l v) =
            fun i => a (radicalQuotientMap L R l) (N v i)) → False := by
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy L M).trans hc.span_normalizes_radical)
  dsimp only
  intro d hdims a m hm N hN
  obtain ⟨_,_,_,q,hq,E,hE,_⟩ := D.sourceOrbit_binary_pair_coordinates h hd F hF hmodel
  exact no_radical_quotient_natural_marking L R D.sourceOrbit b
    D.sourceOrbit_component_normalizes q hq E hE d hdims a m hm N hN

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
