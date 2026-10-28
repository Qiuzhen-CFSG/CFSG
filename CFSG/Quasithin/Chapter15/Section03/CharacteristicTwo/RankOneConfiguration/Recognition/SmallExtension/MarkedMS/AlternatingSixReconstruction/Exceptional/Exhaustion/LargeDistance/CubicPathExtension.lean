module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicStrictSlices

/-!
# Critical path extension and forward eligibility in the cubic cover

The full point-core branch has a backward critical shift for every critical
walk. Iterating this shift preserves the entire surviving prefix. Since the
critical distance is even, the first two original edges eventually become
the final two edges of a critical walk. Reversing that walk and applying
critical nonnormality proves forward eligibility on the original path.

This discharges the eligibility hypothesis in the small-image strict-slice
bound and its actual generating-edge backward-shift consumer. Both central
covers and the full cubic kernel are retained. The whole-core and literal
C.1.32 applications still require point-core identification, the remaining
large-image strict-slice and terminal distance arguments, and natural
exhaustion before either unconditional reconstruction outcome is complete.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2)(iv), (5.8)--(5.9),
printed pp.919--922. Iteration uses the original graph and its exact overlaps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
include h e hz hk in
/-- Iterate actual backward critical shifts. The entire surviving prefix is retained,
with its vertices moved by exactly twice the number of shifts. -/
theorem full_point_iterated_backward_paths
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (n : ℕ) (hn : 2*n ≤ p.walk.length) :
    ∃ d d', ∃ q : CriticalPath Rg (sourceGeometry h) d d',
      ∀ i ≤ p.walk.length-2*n, q.walk.getVert (i+2*n) = p.walk.getVert i := by
  induction n with
  | zero =>
    exact ⟨a,a',p,fun i _ => by simp⟩
  | succ n ih =>
    obtain ⟨d,d',q,hq⟩ := ih (by omega)
    obtain ⟨c,w,r,hw,hr,hover⟩ :=
      full_point_backward_critical_path h e hz hk hb u hfull q
    refine ⟨c,q.walk.getVert (q.walk.length-2),r,?_⟩
    intro i hi
    have hl : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    calc
      r.walk.getVert (i+2*(n+1)) = r.walk.getVert ((i+2*n)+2) := by congr 1
      _ = q.walk.getVert (i+2*n) := hover _ (by omega)
      _ = p.walk.getVert i := hq _ (by omega)

include h e hz hk in
/-- Extend backward until the original first two edges are the final two edges
of a critical walk, then reverse it. Both the middle vertex and the original
start are retained in the resulting critical prefix. -/
theorem full_point_critical_reverse_prefix
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
      q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have heven := sourceDistance_even h
  rw [Nat.even_iff] at heven
  let n := (p.walk.length-2)/2
  have hn : 2*n+2 = p.walk.length := by dsimp [n]; omega
  obtain ⟨d,d',q,hover⟩ := full_point_iterated_backward_paths h e hz hk hb u hfull p n (by omega)
  have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans hl.symm
  have hend : d' = p.walk.getVert 2 := by
    have hh := hover 2 (by omega)
    rw [show 2+2*n = q.walk.length by omega,q.walk.getVert_length] at hh
    exact hh
  let r : CriticalPath Rg (sourceGeometry h) d' d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        d q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) d' q.end_color q.critical⟩
  have hr1 : r.walk.getVert 1 = p.walk.getVert 1 := by
    change q.walk.reverse.getVert 1 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length-1 = 1+2*n by omega]
    exact hover 1 (by omega)
  have hr2 : r.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length-2 = 0+2*n by omega,
      hover 0 (by omega),SimpleGraph.Walk.getVert_zero]
  have hh : ∃ r : CriticalPath Rg (sourceGeometry h) d' d,
      r.walk.getVert 1 = p.walk.getVert 1 ∧ r.walk.getVert 2 = a := ⟨r,hr1,hr2⟩
  rw [hend] at hh
  exact ⟨d,hh⟩

include h e hz hk in
/-- The forward moved cover escapes the starting Baumann slice on every critical
walk in the full point-core branch. Apply critical nonnormality to the actual
reverse prefix constructed by repeated backward shifts. -/
theorem full_point_critical_forward_eligible
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  obtain ⟨d,q,_,hq⟩ := full_point_critical_reverse_prefix h e hz hk hb u hfull p
  have hh := critical_start_not_le_second_slice h e hz hb q
  rwa [hq] at hh

include h e hz hk in
/-- Above distance four, every small-image critical walk in the full point-core
branch has strict forward slice. Forward eligibility is now discharged. -/
theorem full_point_small_forward_slice_strict
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4) :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) :=
  full_point_small_forward_slice_gt_two_at e hz hk hb u hfull p hsmall
    (full_point_critical_forward_eligible h e hz hk (by omega) u hfull p)

include h e hz hk in
/-- The strict bound now discharges the slice premise of the actual
small-image backward shift. The selected second vertex, transported first
edge and complete overlap all use the same original cubic graph. -/
theorem full_point_small_backward_shift
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ∧
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
        act Rg g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (act Rg g (p.walk.getVert 2))) :=
  full_point_small_backward_shift_of_forward_eligibility e hz hk hb u hfull p hsmall
    (full_point_critical_forward_eligible h e hz hk (by omega) u hfull p)

omit hk in
include h e hz in
/-- Whole-core application of the strict small-image slice bound and its
actual backward path. Both full covers and the original odd kernel remain. -/
theorem coreExhaustion_or_cubic_full_point_path_extension :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g (p.walk.getVert 2))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,fun u hu hb4 a' p hp =>
      full_point_small_backward_shift h e hz hk hb4 u hu p hp⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the proved strict small-image slice and
backward shift. The remaining source cases and full reconstruction stay open. -/
theorem rankTwo_or_cubic_full_point_path_extension :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g (p.walk.getVert 2))) :=
  (coreExhaustion_or_cubic_full_point_path_extension h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
