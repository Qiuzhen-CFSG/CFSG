module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedResidualLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedLine

/-!
# The actual residual marked choice and its fixed failure line

Retain the residual membership of the same marked paired conjugator used
in the source failure-line argument. Its cube belongs to the starting core,
and its order-two failure line is fixed by the whole starting stabilizer.
Opposite-midpoint fixation and the whole residual-core estimates remain open.

Source: MS93 (5.6), (5.12)(3), printed pp.917--918,926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- The actual strict mixed source configuration has an order-two failure
line fixed by the whole starting stabilizer in either endpoint orientation.
The same marked paired conjugator is constructed inside the starting residual
from the original hypotheses, and its cube lies in the starting two-core. -/
theorem strict_selected_residual_fixed_failure_line_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) =
          stabilizer d.radical (alpha d.radical) ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical (alpha d.radical) ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
          Q d.radical (act d.radical x (p.walk.getVert 2)) ∧
        x ∈ normalizer ((Z d.radical (alpha d.radical) ⊓
          Z d.radical (p.walk.getVert 2) : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        ∃ H : Subgroup (FreeAmalgam d.radical),
          (H = ⁅Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2),
              Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆ ∨
            H = ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
              Z d.radical (act d.radical x z) ⊓ Q d.radical (alpha d.radical)⁆) ∧
          Nat.card H = 2 ∧ H ≤ Z d.radical q.edge ∧
          H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
          H ≤ Z d.radical q.start ⊓ Z d.radical (p.walk.getVert 2) ⊓
            Z d.radical z ⊓ Z d.radical (act d.radical x z) := by
  obtain ⟨q,x,hxL,hpair,hend,hkernel,hmark,hx3⟩ :=
    strict_selected_marked_residual_pair_knownSimple hb u him p hstrict
  have hx := Ltilde_le_stabilizer (alpha d.radical) hxL
  refine ⟨q,x,hxL,hpair,hend,hkernel,hmark,hx3,?_⟩
  by_cases hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _)
  · obtain ⟨hcard,hedge,hfix,hseeds⟩ :=
      mixed_backward_failure_line_knownSimple hb u him p q hstrict hbad
    refine ⟨_,Or.inl rfl,hcard,hedge,hfix,le_inf hseeds ?_⟩
    exact (fixed_line_le_seed_iff_conjugate _ hfix x hx).mpr (hseeds.trans inf_le_right)
  · have hnorm := Classical.not_not.mp hbad
    have hbadx : ¬ Z d.radical (act d.radical x z) ≤ normalizer
        (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
          Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro hh
      exact paired_normalization_false_knownSimple hb u him p q hstrict x hend hnorm
        (backward_kernel_normalization_transfer_knownSimple hb u him p q _ _
          (le_inf inf_le_left hkernel) inf_le_left (le_sup_right.trans_eq hend) hh)
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (by omega)
    have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
      adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
        (p.walk.adj_getVert_succ (i := 1) (by omega)))
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
      rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    have hinter := mixed_strict_seed_intersection_eq_edge s (by omega) u hf
      p.start_color hat hvt hstrict
    rw [hinter] at hmark
    obtain ⟨hcard,hedge,hfix,hseeds⟩ :=
      conjugate_failure_line_fixed_knownSimple hb u him p q hstrict x hx hmark hbadx
    refine ⟨_,Or.inr rfl,hcard,hedge,hfix,?_⟩
    exact le_inf (le_inf (hseeds.trans inf_le_left)
      ((fixed_line_le_seed_iff_conjugate _ hfix x hx).mp (hseeds.trans inf_le_right)))
      (hseeds.trans inf_le_right)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
