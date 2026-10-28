module
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalRootedSymplectic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.Source318
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound

/-!
# The original chosen orbit and its remaining symplectic source case

The chosen module supplies an actual Fundamental Setup. Its nonzero T-orbit
and an outside maximal local give the literal qrc hypotheses. The complete
numerical reduction, including root-free symplectic recognition, therefore
bounds that orbit unless its original maximal-core quotient contains the
rooted symplectic pair recorded here. The intrinsic centralizer quotient is
transported to the existing whole-orbit representation with its seed fixed.

The outside-maximal guard remains an input. The remaining rooted pair is a
geometric source obligation, not a numerical assumption or a completed 3.1.8.
Source: Aschbacher--Smith 3.1.6--8 and 3.2.5, pp.573--580, as used in 12.2.2,
pp.794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem orbit_cubicRatio_le_of_local_source_bound (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hb : Chapter10.SourceLocalModuleCubicBound (D.fundamentalSetup h)) :
    cubicRatio D.orbitRepresentation ≤ 2 := by
  let J := L ⊔ (T : Subgroup G)
  have hW : (⊤ : Subgroup J) ≤ subspaceStabilizer (ReducedNormal.representation J)
      D.orbitSpace := orbitSpan_invariant _ ⊤ D.space
  let := ReducedNormal.intrinsicSubspace_normal J D.orbitSpace hW
  have hjoin : localJoin T L = J := by
    change localOrbit T L ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G)
    rw [D.localOrbit_eq]
  have hQ : (D.fundamentalSetup h).moduleSubgroup.subgroupOf J =
      ReducedNormal.intrinsicSubspace J D.orbitSpace := by
    rw [ReducedNormal.intrinsicSubspace_eq]
    exact congrArg (fun U : Subgroup G => U.subgroupOf J)
      (D.orbitSpace_image_fundamentalSetup h).symm
  have hb₀ : ∃ (Q : Subgroup (localJoin T L)) (hr : IsPReduced 2 Q),
      Q = (D.fundamentalSetup h).moduleSubgroup.subgroupOf (localJoin T L) ∧
      (letI := hr.normal
       letI := hr.elementary
       cubicRatio (Representation.NormalElementaryQuotient.representation Q
         (QuotientGroup.mk' (centralizer (Q : Set (localJoin T L))))
         (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2) :=
    ⟨_, Chapter10.source_parabolic_module_reduced (D.fundamentalSetup h), rfl, hb⟩
  have hb₁ : ∃ (Q : Subgroup J) (hr : IsPReduced 2 Q),
      Q = (D.fundamentalSetup h).moduleSubgroup.subgroupOf J ∧
      (letI := hr.normal
       letI := hr.elementary
       cubicRatio (Representation.NormalElementaryQuotient.representation Q
         (QuotientGroup.mk' (centralizer (Q : Set J)))
         (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2) := hjoin ▸ hb₀
  obtain ⟨Q, hr, he, hbound⟩ := hb₁
  have he' : Q = ReducedNormal.intrinsicSubspace J D.orbitSpace := he.trans hQ
  clear he
  subst Q
  exact ReducedNormal.cubicRatio_image_le_of_intrinsic_quotient J D.orbitSpace hW 2 hbound

/-- The whole original chosen orbit has the cubic bound unless the literal
root-containing symplectic source pair occurs. All other qrc branches are closed. -/
theorem orbit_cubicRatio_le_or_rooted_symplectic_model (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      Chapter3.HasMaximalOutside T M) :
    cubicRatio D.orbitRepresentation ≤ 2 ∨
      ∃ H : Subgroup G,
      ∃ hH : H ∈ Chapter3.HStar (T : Subgroup G) (D.fundamentalSetup h).maximalLocal,
        Chapter3.QrcHypotheses.HasRootedSymplecticOutsideCoreModel
          ((D.fundamentalSetup h).qrcHypotheses
            (Chapter10.source_module_nonsolvable_uniqueness (D.fundamentalSetup h)) hH) := by
  let A := D.fundamentalSetup h
  have hu := A.lemma_3_2_3_uniqueness (Chapter10.source_module_nonsolvable_uniqueness A)
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (hout A.maximalLocal hu.1 (le_sup_right.trans hu.2.1))
  have hq := A.qrcHypotheses (Chapter10.source_module_nonsolvable_uniqueness A) hH
  rcases hq.cubicRatio_le_two_or_rooted_symplectic_model A.simpleQTKE hu.1 hu.2.2
      A.module_ne_bot with hb | hr
  · exact Or.inl (orbit_cubicRatio_le_of_local_source_bound D h
      (Chapter10.source_localModule_cubic_bound_of_image A hb))
  · exact Or.inr ⟨H,hH,hr⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
