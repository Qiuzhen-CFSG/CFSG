module
public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicStructure
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticTrack

/-!
# The actual critical track in the cyclic-residual alternative

The surviving quintic alternative of original14.6.12(2) has a genuine
F.7 critical track on its literal residual vertex and selected outside
vertex. Its seed maps to the original plane, and its common Sylow maps to
T. The elementary closure and exact(5,3) pair are retained. The marked
Ree/Tits enumeration and ambient Tits recognition are subsequent steps.

Source: Aschbacher--Smith14.6.12(2), pp.1030--1031, and14.2.21, p.988.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The actual cyclic source reduction supplies the critical vertex and
minimal distance, with no additional geometric or model premise. -/
theorem source_solvable_minimal_cyclic_model_or_quintic_track
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (hcyc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J))) :
    ClassificationModels.IsTheoremEModel G ∨
      ((T : Subgroup G).relIndex J = 5 ∧
        ChapterF.Source.HypothesisF11
          ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G) ∧
        IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J) ∧
        (Nat.card (conjugateSpanBy (localModule T M) J) = 32 ∨
          Nat.card (conjugateSpanBy (localModule T M) J) = 64) ∧
        (let X := sourceResidual M Mc ⊔ (T : Subgroup G)
         let L := X ⊔ J
         let F : Bool → Subgroup L := fun i => if i then J.subgroupOf L else X.subgroupOf L
         ∃ (D : ChapterF.Section07.Track.SourceSetup F) (hne : D.V ≠ ⊥),
           D.seed.map L.subtype = localModule T M ∧
           (D.sylow false : Subgroup (F false)).map
             (L.subtype.comp (F false).subtype) = (T : Subgroup G) ∧
           0 < D.track hne ∧
           (∃ v : Vertex F, (graph F).dist (base F false) v = D.track hne ∧
             ¬ D.seed ≤ ballKernel F v 1) ∧
           (∀ v : Vertex F, ¬ D.seed ≤ ballKernel F v 1 →
             D.track hne ≤ (graph F).dist (base F false) v))) := by
  rcases source_solvable_minimal_cyclic_model_or_quintic_closure
    hG T hempty hM hu hmany hcard e hab J hJ hs hcyc with hm | ⟨hi,hf,hel,horder⟩
  · exact Or.inl hm
  · obtain ⟨D,hne,hseed,hSylow⟩ := Section02.SolvableAmalgam.source_residual_vertex_track
      hG T hempty hM hu hmany hcard e J hJ
    exact Or.inr ⟨hi,hf,hel,horder,D,hne,hseed,hSylow,(D.track_spec hne).1,
      (D.critical_witness hne).1,(D.critical_witness hne).2⟩

end CFSG.Quasithin.Chapter14.Section06
