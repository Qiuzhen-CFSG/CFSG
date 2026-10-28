module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections

/-!
# The two printed action orientations are distinguishable

A fixed section cannot have both the doubled natural and doubled dual
actions with the same marking. The two quotient maps would induce an
equivariant isomorphism between their coordinate groups. Restriction to
one dual factor, followed by either natural coordinate, is zero by the
checked SL3(2) stabilizer calculation, contradicting injectivity.

This verifies that the discrepancy in MS93 (4.5.4)(iv) is substantive.
It does not choose an orientation for the actual higher layer: that
requires the source commutator-map construction. The printed proof on
p.899 and final (4.5)(vii) on p.895 specify the natural orientation.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
open DistanceFour.Linear
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R} {common : CommonFacts R source geometry}

/-- The natural and dual readings of (4.5.4)(iv) cannot both describe the
same literal quotient with the marking fixed by CommonFacts.natural. -/
theorem MarkedPairSection.not_both_orientations
    {A N : Subgroup (FreeAmalgam R)}
    (d : MarkedPairSection source common A N true)
    (n : MarkedPairSection source common A N false) : False := by
  let ed := QuotientGroup.quotientKerEquivOfSurjective d.quotient d.onto
  let en := QuotientGroup.quotientKerEquivOfSurjective n.quotient n.onto
  let ek := QuotientGroup.quotientMulEquivOfEq (d.kernel.trans n.kernel.symm)
  let E := ed.symm.trans (ek.trans en)
  have hE (x : A) : E (d.quotient x) = n.quotient x := by
    have hx : ed (QuotientGroup.mk x) = d.quotient x := rfl
    change en (ek (ed.symm (d.quotient x))) = n.quotient x
    rw [← hx, ed.symm_apply_apply]
    rfl
  have hact (g : S) (v : W × W) :
      (E (Multiplicative.ofAdd (dual g v.1, dual g v.2))).toAdd =
        (g.val.mulVec (E (Multiplicative.ofAdd v)).toAdd.1,
         g.val.mulVec (E (Multiplicative.ofAdd v)).toAdd.2) := by
    obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
    have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
    have hmbar : embedM R m ∈ Mbar R := ⟨m, rfl⟩
    let y : A := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp d.normalized _ hmbar _ x.property⟩
    have hdy : d.quotient y = Multiplicative.ofAdd (dual g v.1, dual g v.2) := by
      apply Multiplicative.toAdd.injective
      simpa only [Bool.true_eq, reduceIte, hmg, hx, toAdd_ofAdd]
        using d.action m x y rfl
    rw [← hdy, hE, ← hx, hE]
    simpa only [Bool.false_eq_true, reduceIte, hmg] using n.action m x y rfl
  have hfirst (v : W) : (E (Multiplicative.ofAdd (v, 0))).toAdd = 0 := by
    apply Prod.ext
    · apply equivariantDualMap_zero
        (fun w => (E (Multiplicative.ofAdd (w, 0))).toAdd.1) _ v
      intro g w
      simpa only [dual, Matrix.mulVec_zero] using congrArg Prod.fst (hact g (w, 0))
    · apply equivariantDualMap_zero
        (fun w => (E (Multiplicative.ofAdd (w, 0))).toAdd.2) _ v
      intro g w
      simpa only [dual, Matrix.mulVec_zero] using congrArg Prod.snd (hact g (w, 0))
  have he : Multiplicative.ofAdd ((fun _ : Fin 3 => (1 : ZMod 2)), (0 : W)) =
      (1 : Multiplicative (W × W)) :=
    E.injective ((Multiplicative.toAdd.injective (hfirst _)).trans E.map_one.symm)
  have hbad := congrArg (fun z : Multiplicative (W × W) => z.toAdd.1 0) he
  exact one_ne_zero hbad

/-- Applied to the literal moving quotient above hat W, the checked natural
model excludes the conflicting dual reading of the printed clause. The
natural-model witness remains the output of the source quotient construction. -/
theorem moving_quotient_not_dual {c d e : Vertex R}
    (naturalModel : MarkedPairSection source common
      (⁅hatSix R (alpha R) c d e, Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) c d)
      (hatW R (alpha R) c d) false) :
    ¬ Nonempty (MarkedPairSection source common
      (⁅hatSix R (alpha R) c d e, Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) c d)
      (hatW R (alpha R) c d) true) := by
  rintro ⟨dualModel⟩
  exact dualModel.not_both_orientations naturalModel

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
