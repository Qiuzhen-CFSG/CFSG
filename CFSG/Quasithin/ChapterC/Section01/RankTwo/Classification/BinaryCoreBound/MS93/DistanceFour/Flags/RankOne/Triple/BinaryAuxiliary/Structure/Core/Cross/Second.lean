module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Second.Algebra

/-!
# The second-layer bound from the genuine midpoint comparison

The midpoint Y is a two-subgroup of the original full second actor. Its
action on the original natural X has displacement in a binary line. The
crossing and the transported marked moving factor force that displacement
to escape the midpoint U. Thus the displacement of midpoint U itself lies
in the original Z_alpha, which the comparison places in midpoint X.
Normal generation in the full SL₂(2) quotient gives the full-actor bound.
The actual midpoint conjugation and the original M-conjugation then carry
this bound back to delta0.

This conditional theorem retains the source preparatory configuration,
the original natural first-section denominator, and both marked natural
factors. Constructing the midpoint comparison remains the responsibility
of the source-theorem assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), final paragraph of printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The source “Moreover” bound, conditional only on the supplied genuine
midpoint comparison and the two marked natural factors. -/
theorem second_commutator_of_middle_comparison
    (source : LocalSource L R) (geometry : Geometry R)
    (_common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (_early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (_natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0)
    (c : MiddleComparison source geometry i p) :
    ⁅secondFlagLayer source i p.delta0, localFlagActor source (!i) p.delta0⁆ ≤
      X source i p.delta0 := by
  have hlarge : 2 < geometry.b R := by omega
  let t := c.transport
  let f := t.conjugation.toMonoidHom
  let P := (localFlagActor source (!i) c.flag).map f
  let Y' := (Y source i c.flag).map f
  let U' := (secondFlagLayer source i c.flag).map f
  let K := (localFlagKernel source (!i) c.flag).map f
  let X' := (X source i c.flag).map f
  let E := X source i p.delta0
  have hQβP : Q R (beta R) ≤ localFlagActor source (!i) p.delta0 :=
    hkernel ▸ Incident.flagKernel_le_incidentActor source i p.delta0 p.delta0_neighbor
  have hQβP' : Q R (beta R) ≤ P :=
    (t.map_first_kernel source i hkernel).symm.le.trans
      (map_mono (Incident.flagKernel_le_incidentActor source i c.flag c.incident))
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases h : color R p.middle <;> simp_all
  have hYQβ : Y' ≤ Q R (beta R) :=
    ((map_mono (Y_le_radius source i c.flag)).trans_eq t.map_V_alpha).trans
      ((V_le_Q geometry hlarge _ hcol).trans
        (Q_le_adjacent_h R rfl (adjacent_symm R p.middle_neighbor)))
  have hEQ : E ≤ Q R (alpha R) :=
    ((X_le_second source geometry hlarge i p.delta0).trans
      (secondFlagLayer_le_radius source i p.delta0)).trans (V_le_Q geometry hlarge _ rfl)
  have hEP : E ≤ P := hEQ.trans
    ((Q_le_adjacent_h R rfl (base_adjacent R)).trans hQβP')
  have hE : IsPGroup 2 E :=
    (Q_isPGroup R source.two_group source.core_le _ rfl).to_le hEQ
  have hY : IsPGroup 2 Y' :=
    ((Q_isPGroup R source.two_group source.core_le _ rfl).to_le
      ((Y_le_radius source i c.flag).trans (V_le_Q geometry hlarge _ rfl))).map f
  obtain ⟨me⟩ : Nonempty (MovingFactor source i c.flag) := by
    simpa only [inv_mul_cancel_right] using
      movingFactor_conjugate source geometry hlarge i (c.flag * p.delta0⁻¹) p.delta0 moving
  have hm : MarkedFactor P (⁅Y',P⁆ ⊔ U') U' K := by
    simpa only [Subgroup.map_sup, map_commutator] using markedFactorMap t.conjugation me
  have hPX : P ≤ normalizer X' :=
    (map_mono (X_normalized source geometry hlarge i c.flag)).trans (le_normalizer_map f)
  have hPU : P ≤ normalizer U' :=
    (map_mono (Incident.secondFlagLayer_normalized source geometry hlarge i c.flag)).trans
      (le_normalizer_map f)
  have hPY : P ≤ normalizer Y' :=
    (map_mono (Y_normalized source i c.flag)).trans (le_normalizer_map f)
  have hUK : ⁅U',K⁆ ≤ X' := by
    rw [← map_commutator]
    exact map_mono ((Incident.secondFlagLayer_commutator_le_Z source geometry hlarge i c.flag).trans
      (show Z R (alpha R) ≤ X source i c.flag from le_sup_right))
  have hbound : ⁅U',P⁆ ≤ X' := Second.absorption P Y' U' K X'
    (localFlagActor source (!i) p.delta0) E (Z R (alpha R)) x.val hm
    (hYQβ.trans hQβP) hY hEP hE c.crossing
    (map_mono (second_le_Y source i c.flag))
    (map_mono (X_le_second source geometry hlarge i c.flag)) c.center_le_X
    hPY hPU hPX hUK (map_mono (map_mono (flagKernel_le source (!i))))
  have he : ⁅secondFlagLayer source i c.flag, localFlagActor source (!i) c.flag⁆ ≤
      X source i c.flag := by
    apply (map_le_map_iff_of_injective (f := f) t.conjugation.injective).mp
    rw [map_commutator]
    exact hbound
  let a := p.delta0 * c.flag⁻¹
  have hh := map_mono (f := (MulAut.conj (embedM R a)).toMonoidHom) he
  rw [map_commutator] at hh
  change ⁅localConjugate (secondFlagLayer source i c.flag) a,
    localConjugate (localConjugate (flagParabolic source (!i)) c.flag) a⁆ ≤
    localConjugate (X source i c.flag) a at hh
  simpa only [second_conjugate source geometry hlarge, X_conjugate source geometry hlarge,
    ← localConjugate_mul, a, inv_mul_cancel_right, localFlagActor] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
