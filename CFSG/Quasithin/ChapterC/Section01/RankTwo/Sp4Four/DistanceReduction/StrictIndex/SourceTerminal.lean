module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Terminal

/-!
# The source spans in the terminal strict-index contradiction

The printed commutator comparison and selected local generators make the
literal centralizer span invariant. An escaping actor then bounds its
residual displacement; nilpotence of Q collapses it to the original orbit
span. The actual orbit seed, quotient, centralizer T0 and critical witness
then give the terminal contradiction with the reciprocal source5.8 index.

The displayed comparison and selection, the local residual-kernel generation,
the original T0-displacement, and the earlier critical witness remain explicit.
They are the remaining source mathematics, not a strict-index assumption.
Source: Meierfrankenfeld--Stellmacher (1993), (5.9), pp.920--922.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geometry : Geometry R)

/-- The source comparison produces invariance of its original seed span;
neither invariance nor the residual displacement is assumed. -/
theorem source_seed_span_normalized_of_printed_comparison
    (hb : 4 < geometry.b R) {c mu f : Vertex R}
    (hc : color R c = false) (hmu : color R mu = false)
    (hd : (cosetGraph R).dist c mu ≤ 2)
    {J : Type*} [Group J]
    (q : stabilizer R c →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R c).subgroupOf (stabilizer R c))
    (hp : IsPGroup 2 (Q R c))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R c)).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R c)).map q : Set J) = ⊥)
    (H₂ : Subgroup (FreeAmalgam R))
    (hgen : (stabilizer R c ⊓ centralizer (H₂ : Set _)) ⊔ Z R f = stabilizer R c)
    (hlocal : Ltilde R c ⊔ Q R c = stabilizer R c)
    (hescape : ¬ Z R f ≤ Q R c)
    (hcomparison : ⁅sourceCentralizerSpan R c mu H₂,Z R f⁆ ≤
      ⁅sourceCentralizerSpan R c mu H₂,Q R c⁆ ⊔ ⁅Z R c,Z R f⁆) :
    stabilizer R c ≤ normalizer (sourceSeedSpan R c mu : Set _) := by
  have hWQ := sourceCentralizerSpan_le_Q (R := R) geometry hb hc hd H₂
  have hWN := sourceCentralizerSpan_normalized_of_comparison (R := R) hc hmu hd H₂
    (Z R f) hgen hcomparison
  have hE : Z R f ≤ stabilizer R c := hgen ▸ le_sup_right
  have hdisp := residual_displacement_of_comparison q hq hk hp hS hC
    (sourceCentralizerSpan R c mu H₂) (Z R f)
    (hWQ.trans (fun _ hx => hx.1)) hWN hE hescape hcomparison
  exact sourceSeedSpan_normalized_of_displacement (R := R) hc hmu hd hp H₂
    hWQ hlocal hWN hdisp

/-- All group and graph deductions after the printed source comparison,
with the original spans and T0. The preceding selection and comparison
are genuine remaining proof obligations. -/
theorem source_spans_contradict_source58
    (hb : 4 < geometry.b R) {a e xi f : Vertex R}
    (p : CriticalPath R geometry a e)
    (w : CriticalPath R geometry xi (p.walk.getVert 2))
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hcentral : Z R xi ≤ centralizer ((Z R (p.walk.getVert 2) ⊓
      B R a (geometry.Z_normal a) : Subgroup (FreeAmalgam R)) : Set _))
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R (p.walk.getVert 2))
    {J : Type*} [Group J]
    (q : stabilizer R (p.walk.getVert 2) →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R (p.walk.getVert 2)).subgroupOf (stabilizer R (p.walk.getVert 2)))
    (hp : IsPGroup 2 (Q R (p.walk.getVert 2)))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R (p.walk.getVert 2))).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R (p.walk.getVert 2))).map q : Set J) = ⊥)
    (hgen : (stabilizer R (p.walk.getVert 2) ⊓
      centralizer (conjugatedKernelCommutator geometry a (p.walk.getVert 2) y : Set _)) ⊔
      Z R f = stabilizer R (p.walk.getVert 2))
    (hlocal : Ltilde R (p.walk.getVert 2) ⊔ Q R (p.walk.getVert 2) =
      stabilizer R (p.walk.getVert 2))
    (hescape : ¬ Z R f ≤ Q R (p.walk.getVert 2))
    (hcomparison : ⁅sourceCentralizerSpan R (p.walk.getVert 2) (act R y a)
        (conjugatedKernelCommutator geometry a (p.walk.getVert 2) y),Z R f⁆ ≤
      ⁅sourceCentralizerSpan R (p.walk.getVert 2) (act R y a)
        (conjugatedKernelCommutator geometry a (p.walk.getVert 2) y),Q R (p.walk.getVert 2)⁆ ⊔
        ⁅Z R (p.walk.getVert 2),Z R f⁆)
    (hdisp : ⁅sourceSeedSpan R (p.walk.getVert 2) (act R y a),
      (kernelCentralizer geometry a (p.walk.getVert 2)).map
        (MulAut.conj y⁻¹).toMonoidHom⁆ ≤
      conjugatedKernelCommutator geometry a (p.walk.getVert 2) y)
    (hH : kernelCommutator geometry a (p.walk.getVert 2) ≤ Z R (p.walk.getVert 1))
    (h58 : 4 ≤ (B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2))).relIndex
      (U R a)) : False := by
  have hlen : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color hlen).mpr (by decide)
  have hmu : color R (act R y a) = false := by
    rw [action_preserves_color]
    exact p.start_color
  have hdist : (cosetGraph R).dist (p.walk.getVert 2) (act R y a) ≤ 2 := by
    have hh := dist_act R y a (p.walk.getVert 2)
    rw [show act R y (p.walk.getVert 2) = p.walk.getVert 2 from hy,
      p.dist_start hlen] at hh
    rw [SimpleGraph.dist_comm]
    exact hh.le
  have hn := source_seed_span_normalized_of_printed_comparison geometry hb hc hmu hdist
    q hq hk hp hS hC (conjugatedKernelCommutator geometry a (p.walk.getVert 2) y)
    hgen hlocal hescape hcomparison
  have hF := (sourceSeedSpan_le_Q (R := R) geometry hb hc hdist).trans (fun _ hx => hx.1)
  exact local_normal_span_contradicts_source58 geometry hb p w hd hcentral y hy
    q hq hk hp hS hC (sourceSeedSpan R (p.walk.getVert 2) (act R y a)) hF hn
    (conjugated_start_seed_le_source_span (by omega) p y hy)
    (hdisp.trans (conjugated_kernel_commutator_le_next_seed geometry (by omega) p y hy hH)) h58

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
