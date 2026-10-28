module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinaryFullParabolics

/-!
# Source applications of the binary full-parabolic calculation

Start with Chapter 9's binary markings on the actual starred subgroups
inside the reduced completion. The original quotient equivalence pulls them
back to the original local factors. BinaryFullParabolics then gives the full
original and graph stabilizers, with an explicit representative identity for
each original inclusion. This excludes a nonsolvable original parabolic and
the actual quintic local-factor premise [K:S] = 5.

These applications discharge the original/full-group transport in (13.1)(b)
and the binary exclusion for the quintic consumer. The earlier Chapter 9
binary markings remain inputs of qt-dgs85-critical-commuting-trivial. Their
unconditional discharge, b = 3, and the remaining Chapter 12/13 source
assembly are not asserted here.

Source: DGS85, Groups and Graphs, (13.1), printed p.191;
Aschbacher--Smith F.1.9 and F.1.12, printed pp.261--264.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Reduction ReducedLayer Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private def binaryOriginalQuotients (h : HypothesisF11 L S)
    (e : ∀ i, (star L S i ⧸ pCore 2 (star L S i)) ≃* SL(2, ZMod 2))
    (j : Fin 2) : (L j ⧸ pCore 2 (L j)) ≃* SL(2, ZMod 2) := by
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun z => Fin.elim0 z) k) j
  · exact (originalQuotient h false).trans (e false)
  · exact (originalQuotient h true).trans (e true)

private theorem binaryOriginalQuotients_mk (h : HypothesisF11 L S)
    (e : ∀ i, (star L S i ⧸ pCore 2 (star L S i)) ≃* SL(2, ZMod 2))
    (i : Bool) (x : L (if i then 1 else 0)) :
    binaryOriginalQuotients h e (if i then 1 else 0) (QuotientGroup.mk x) =
      e i (QuotientGroup.mk (originalActor (L := L) (S := S) i x)) := by
  cases i <;> rfl

/-- The actual Chapter 9 binary markings give the full original and graph
parabolics, preserving the original inclusion on every local representative. -/
theorem source_binary_full_parabolics (h : HypothesisF11 L S)
    (e : ∀ i, (star L S i ⧸ pCore 2 (star L S i)) ≃* SL(2, ZMod 2)) :
    commonBorel L S = S ∧ G₀ L S = generated L S ∧
      (∀ i : Bool, ∃ f : (parabolic L S (if i then 1 else 0) ⧸
          pCore 2 (parabolic L S (if i then 1 else 0))) ≃* SL(2, ZMod 2),
        (∀ x : L (if i then 1 else 0),
          f (QuotientGroup.mk (inclusion (show L (if i then 1 else 0) ≤
            parabolic L S (if i then 1 else 0) from le_sup_left.trans le_sup_left) x)) =
            e i (QuotientGroup.mk (originalActor (L := L) (S := S) i x))) ∧
        starredParabolic L S (if i then 1 else 0) = parabolic L S (if i then 1 else 0) ∧
        Group.IsSolvable (parabolic L S (if i then 1 else 0))) ∧
      ∀ v : Vertex (reducedFamily L S),
        graphLocalGroup (reducedFamily L S) v = stabilizer (reducedFamily L S) v ∧
        Nonempty ((stabilizer (reducedFamily L S) v ⧸
          pCore 2 (stabilizer (reducedFamily L S) v)) ≃* SL(2, ZMod 2)) := by
  let f := binaryOriginalQuotients h e
  refine ⟨both_binary_commonBorel h f, (both_binary_reduction_eq_original h f).2.2,
    ?_, fun v => ⟨both_binary_graphLocalGroup_eq_stabilizer h f v,
      both_binary_vertex_quotient h f v⟩⟩
  intro i
  refine ⟨binaryFullParabolicEquiv h f _, ?_, both_binary_star_eq_parabolic h f _,
    both_binary_full_parabolics_solvable h f _⟩
  intro x
  exact (binaryFullParabolicEquiv_mk h f _ x).trans (binaryOriginalQuotients_mk h e i x)

/-- The source binary markings are incompatible with a nonsolvable full
original endpoint, without substituting a model for that endpoint. -/
theorem no_source_binary_of_nonsolvable_parabolic (h : HypothesisF11 L S)
    (i : Fin 2) (hns : ¬ Group.IsSolvable (parabolic L S i))
    (e : ∀ j, (star L S j ⧸ pCore 2 (star L S j)) ≃* SL(2, ZMod 2)) : False :=
  hns (both_binary_full_parabolics_solvable h (binaryOriginalQuotients h e) i)

/-- Apply the literal source starred marking to the quintic local factor K;
the source premise is [K:S] = 5, not an index in a larger parabolic. -/
theorem no_source_binary_of_local_quintic {K R : Subgroup G}
    (h : HypothesisF11 ![K, R] S) (hfive : S.relIndex K = 5)
    (e : (star ![K, R] S false ⧸ pCore 2 (star ![K, R] S false)) ≃* SL(2, ZMod 2)) :
    False := by
  have hi : S.relIndex K = 3 :=
    binary_local_sylow_index h 0 ((originalQuotient h false).trans e)
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
