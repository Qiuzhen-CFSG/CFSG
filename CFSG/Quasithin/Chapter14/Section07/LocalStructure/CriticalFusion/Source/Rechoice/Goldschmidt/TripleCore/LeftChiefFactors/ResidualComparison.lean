module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Comparison

/-!
# Chief-series actor changes for the original left residual

The source filtration is a filtration of the actual group L₁T in G. Its
chief series is transported to the left vertex in I through the inverse
of `subgroupOfEquivOfLe`, preserving the count and literal ambient elements.
A refinement in the intrinsic two-residual is then transported through
`leftResidualEquiv` to the original L₁.

The residual comparison now discharges both local action-survival and
noncentral-refinement premises. It holds for every finite actor, hence also
for the actual left vertex whose S₃ quotient is `quotient_left d c structural`.
The earlier conditional interface is preserved. The preliminary five-factor
bound stays with the source filtration owner, who may apply the comparison
to its complete series. Only the root LeftChiefFactors chapter branch is
imported. The earlier Structural1222 premise is the same one needed by
`leftResidualEquiv`, with producer qt-12-02.

Source: Aschbacher–Smith 14.7.70, printed p.1074 (PDF p.1091).
-/

public section
noncomputable section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The original source actor L₁T and its actual subgroupOf copy in I. -/
@[expose] def sourceToLeftEquiv (c : CriticalPath (L := L) F) : group F L ≃* left c :=
  (subgroupOfEquivOfLe (show group F L ≤ I c from le_sup_left)).symm

omit [Finite G] in
/-- This actor change is inclusion into I on the literal ambient element. -/
@[simp] theorem sourceToLeftEquiv_apply (c : CriticalPath (L := L) F) (x : group F L) :
    ((sourceToLeftEquiv c x).val : G) = (x : G) := rfl

omit [Finite G] in
/-- The complete source series can be used in the actual left vertex without
assuming or altering its chief-factor count. -/
theorem source_series_left (c : CriticalPath (L := L) F)
    (s : ChiefSeries (group F L)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    (s.mapActor (sourceToLeftEquiv c)).head = ⊥ ∧
      (s.mapActor (sourceToLeftEquiv c)).last = ⊤ ∧
      (s.mapActor (sourceToLeftEquiv c)).noncentralTwoCount = s.noncentralTwoCount := by
  exact ⟨(s.mapActor_complete _ h0 h1).1, (s.mapActor_complete _ h0 h1).2,
    s.mapActor_noncentralTwoCount _⟩

/-- A complete series of the actual residual transports to the original L₁,
preserving every term through the genuine ambient-inclusion isomorphism. -/
theorem residual_series_original (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (t : ChiefSeries (pResidual 2 (left c))) (h0 : t.head = ⊥) (h1 : t.last = ⊤) :
    (t.mapActor (leftResidualEquiv d c structural)).head = ⊥ ∧
      (t.mapActor (leftResidualEquiv d c structural)).last = ⊤ ∧
      (t.mapActor (leftResidualEquiv d c structural)).noncentralTwoCount = t.noncentralTwoCount ∧
      ∀ x : pResidual 2 (left c),
        (leftResidualEquiv d c structural x : G) = (x.val.val : G) := by
  exact ⟨(t.mapActor_complete _ h0 h1).1, (t.mapActor_complete _ h0 h1).2,
    t.mapActor_noncentralTwoCount _, leftResidualEquiv_apply d c structural⟩

/-- Conditional final actor assembly, ready for the two local residual-action
lemmas. Its input series is in SourceFiltration's literal L₁T actor, and no
five-factor lower bound is assumed. -/
theorem source_series_original_of_local_survival (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (s : ChiefSeries (group F L)) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hsection : ∀ A B : NormalNode (left c), A ⋖ B → IsNoncentralTwo A B →
      IsNoncentralTwo (restrictNormalNode (pResidual 2 (left c)) A)
        (restrictNormalNode (pResidual 2 (left c)) B))
    (hrefine : ∀ t : ChiefSeries (pResidual 2 (left c)), IsNoncentralTwo t.head t.last →
      ∃ j : Fin t.length, IsNoncentralTwo (t j.castSucc) (t j.succ)) :
    ∃ t : ChiefSeries (F.Li L 1), t.head = ⊥ ∧ t.last = ⊤ ∧
      s.noncentralTwoCount ≤ t.noncentralTwoCount ∧
      ∃ ι : Fin (s.length + 1) →o Fin (t.length + 1),
        ∀ i, t (ι i) = actorNormalEquiv (leftResidualEquiv d c structural)
          (restrictNormalNode (pResidual 2 (left c))
            (actorNormalEquiv (sourceToLeftEquiv c) (s i))) := by
  let s' := s.mapActor (sourceToLeftEquiv c)
  obtain ⟨hs0, hs1, hsc⟩ := source_series_left c s h0 h1
  obtain ⟨t, ι, hi, _, _, ht0, ht1, hc⟩ :=
    s'.exists_comparison_of_restriction_survival (pResidual 2 (left c)) hs0 hs1
      (fun i => hsection _ _ (s'.step i)) hrefine
  let e := leftResidualEquiv d c structural
  refine ⟨t.mapActor e, (t.mapActor_complete e ht0 ht1).1,
    (t.mapActor_complete e ht0 ht1).2, ?_, ι, ?_⟩
  · rw [t.mapActor_noncentralTwoCount]
    exact hsc.symm.le.trans hc
  · intro i
    exact congrArg (actorNormalEquiv e) (hi i)

/-- The actual left vertex has a complete series in its original L₁ residual
with at least the original count. All intersected terms and both endpoints
are retained through the literal ambient-inclusion isomorphism. -/
theorem left_series_original (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (s : ChiefSeries (left c)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    ∃ (t : ChiefSeries (F.Li L 1))
      (ι : Fin (s.length + 1) →o Fin (t.length + 1)),
      (∀ i, t (ι i) = actorNormalEquiv (leftResidualEquiv d c structural)
        (restrictNormalNode (pResidual 2 (left c)) (s i))) ∧
      ι 0 = 0 ∧ ι (Fin.last s.length) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ ∧ s.noncentralTwoCount ≤ t.noncentralTwoCount ∧
      ∀ x : pResidual 2 (left c),
        (leftResidualEquiv d c structural x : G) = (x.val.val : G) := by
  obtain ⟨t, ι, hi, hi0, hi1, ht0, ht1, hc⟩ :=
    s.exists_complete_pResidual_refinement h0 h1
  let e := leftResidualEquiv d c structural
  obtain ⟨h0', h1', hcount, hmap⟩ := residual_series_original d c structural t ht0 ht1
  exact ⟨t.mapActor e, ι, fun i => congrArg (actorNormalEquiv e) (hi i),
    hi0, hi1, h0', h1', hc.trans hcount.symm.le, hmap⟩

/-- Transfer any complete series in SourceFiltration's actual L₁T actor to
the original L₁ with a nondecreasing noncentral binary count. The two local
action premises are proved, and no five-factor bound is assumed. -/
theorem source_series_original (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (s : ChiefSeries (group F L)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    ∃ t : ChiefSeries (F.Li L 1), t.head = ⊥ ∧ t.last = ⊤ ∧
      s.noncentralTwoCount ≤ t.noncentralTwoCount ∧
      ∃ ι : Fin (s.length + 1) →o Fin (t.length + 1),
        ∀ i, t (ι i) = actorNormalEquiv (leftResidualEquiv d c structural)
          (restrictNormalNode (pResidual 2 (left c))
            (actorNormalEquiv (sourceToLeftEquiv c) (s i))) :=
  source_series_original_of_local_survival d c structural s h0 h1
    (fun A B => isNoncentralTwo_restrict_pResidual A B)
    (fun t => t.exists_noncentralTwo_pResidual)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
