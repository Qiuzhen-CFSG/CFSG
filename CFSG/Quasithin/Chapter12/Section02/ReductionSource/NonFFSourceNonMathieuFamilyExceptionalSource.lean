module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTriality
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsRee
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource

/-!
# Exceptional cubic reductions on the literal chosen module

For a triality marking of the original orbit component's central quotient,
the binary degree is at least 24r and every possible cubic actor lies in
that component. For the positive Ree F4 marking, the original cubic bound
produces a quadratic actor of rank 5(2m+1), equal to the fixed-space kernel
inside each of its involution centralizers and normal relative to them.

Both applications retain `D.orbitRepresentation` and `D.orbitComponent`.
These are reductions, not the completed exclusions: the triality inner
module argument and the Ree centralizer contradiction remain with this
theorem family's owner. Source: Aschbacher--Smith K.3, printed p.457/PDF468,
and Guralnick--Malle II, Lemmas8.6 and8.8, Theorem8.1/Table17.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterK.Exceptional.CubicSourceExclusions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_triality_inner_actor
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {r : ℕ} (hr : 1 ≤ r)
    (hq : Triality.Standard.IsTrialityGroupAt (2 ^ r)
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    24 * r ≤ Module.finrank (ZMod 2) (Additive D.sourceOrbit) ∧
      ∃ A : Subgroup D.orbitActor, IsElementaryTwo A ∧
        IsCubic D.orbitRepresentation A ∧ A ≤ D.orbitComponent ∧
        rank A ≤ 5 * r ∧ fixedCodim D.orbitRepresentation A ≤ 2 * rank A := by
  refine ⟨?_, triality_source_inner_actor hs hr hq⟩
  have hd := triality_source_degree hs hr hq
  rw [D.sourceOrbitCoordinates.finrank_eq] at hd
  exact hd

theorem sourceOrbit_ree_normal_actor
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* ReeF4.Model m)) :
    ∃ A : Subgroup D.orbitActor, IsElementaryTwo A ∧ A ≤ D.orbitComponent ∧
      rank A = 5 * (2 * m + 1) ∧ fixedCodim D.orbitRepresentation A = 10 * (2 * m + 1) ∧
      IsQuadratic D.orbitRepresentation A ∧
      ∀ t ∈ A, t ≠ 1 → A = involutionFixedKernel D.orbitRepresentation t ∧
        (A.subgroupOf (centralizer {t})).Normal ∧
        fixedSpace D.orbitRepresentation A = fixedSpace D.orbitRepresentation (zpowers t) := by
  obtain ⟨e⟩ := hq
  exact ree_source_normal_actor hs hm e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
