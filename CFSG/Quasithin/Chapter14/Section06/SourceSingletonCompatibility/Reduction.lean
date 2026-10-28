module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Critical

/-!
# The remaining branches of the original odd-core counterexample

The actual transitive factor decomposition has at most two factors.
The primitive singleton theorem discharges starred cyclicity. Identifying
its endpoint kernel with the literal residual excludes the extraspecial
endpoint, leaving cyclic residual or elementary nine. The cyclic branch
feeds the existing cubic recognition and quintic F.1.1 closure theorem.
The elementary-nine branch supplies the exact ratio and a reciprocal
critical pair on the original quotient, group and support.

This is a reduction, not original 14.6.12: the elementary-nine contradiction
and the full index-two conclusion in the two-factor branch remain open.
Source: Aschbacher--Smith 14.6.11--13, printed pp.1030--1032.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The actual odd-core counterexample has two factors, a recognized model,
the original quintic closure, or an elementary-nine singleton with reciprocal
critical geometry. No noncyclic-star premise remains. -/
theorem source_oddCore_counterexample_singleton_reduction
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ _hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J),
      ∃ a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T),
      ∃ f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))),
      ∃ d : ChapterD.RatioDecomposition.Decomposition f.representation,
        d.FittingFull ∧
        (Nat.card d.Index = 2 ∨
          (Nat.card d.Index = 1 ∧
            (ClassificationModels.IsTheoremEModel G ∨
              ((T : Subgroup G).relIndex J = 5 ∧
                ChapterF.Source.HypothesisF11
                  ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G) ∧
                (Nat.card (conjugateSpanBy (localModule T M) J) = 32 ∨
                  Nat.card (conjugateSpanBy (localModule T M) J) = 64)) ∨
              (IsElementaryAbelian 3 (pResidual 2 (J ⧸ pCore 2 J)) ∧
                Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 ∧
                Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤
                  (pResidual 2 (J ⧸ pCore 2 J))) = 4 ∧
                cubicRatio a.representation = 2 ∧
                (let D : ChapterF.Section09.Setup G :=
                   ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
                 let h : D.Hypothesis := source_rankTwo_f9_hypothesis
                   hG T hempty hM hu hmany hcard e hab J hJ.1
                 3 ≤ h.b ∧ Odd h.b ∧
                   ∃ i : h.CriticalEndpoint,
                     i.representative ∉ Mc ∧ ¬ i.conjugate D.UH ≤ D.QH ∧
                     ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
                       J ≤ normalizer (A : Set G) →
                       (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A))))) := by
  classical
  obtain ⟨J,hJ,hJH,hs,hU,a,f,d,hd,_π,_hblocks,_hker,_hperm,_ht,hcount,_hcyc⟩ :=
    source_oddCore_counterexample_transitive_factors
      hG T hempty hM hu hmany hcard e hab H hH hne
  let := hU
  refine ⟨J,hJ,hJH,hs,hU,a,f,d,hd,?_⟩
  by_cases htwo : Nat.card d.Index = 2
  · exact Or.inl htwo
  have hpos : 0 < Nat.card d.Index := Nat.card_pos
  have hone : Nat.card d.Index = 1 := by omega
  obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
  refine Or.inr ⟨hone,?_⟩
  have hc := source_singleton_factor_star_cyclic hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone i
  rcases source_ratio_singleton_cyclicStar_alternatives
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd i hi hc with hcyc | hnine
  · rcases source_solvable_minimal_cyclic_model_or_quintic_closure
      hG T hempty hM hu hmany hcard e hab J hJ hs hcyc with hm | ⟨hindex,hF,_hU,hsize⟩
    · exact Or.inl hm
    · exact Or.inr (Or.inl ⟨hindex,hF,hsize⟩)
  · obtain ⟨hq,hcrit⟩ := source_singleton_nine_critical_reciprocity
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine.2.1
    exact Or.inr (Or.inr ⟨hnine.1,hnine.2.1,hnine.2.2,hq,hcrit⟩)

end CFSG.Quasithin.Chapter14.Section06
