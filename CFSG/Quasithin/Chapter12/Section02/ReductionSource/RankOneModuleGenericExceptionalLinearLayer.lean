module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearLayer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinear
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.Source318
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete

/-!
# Fixed points and the numerical bound on the entire reduced module

Outside residual centralization first gives C_{Ω₁(Z(T))}(L)=1. Applying
the elementary Sylow-center argument to R₂(LT), rather than the chosen V,
gives C_{R₂(LT)}(L)=1. Monotonicity from the original chosen orbit gives the
exact Sylow centralizer of R₂(LT), so the guarded 3.1.8 theorem supplies the
cubic bound for its actual quotient action. None of these steps assumes
T-invariance of V or invokes the later 12.2.2 classification.

The final application converts a finite-copy decomposition and its separate
multiplicity bound into the literal exceptional exit. Those two premises
remain unproved here; in particular recognition on V alone does not supply
the decomposition. Source: Aschbacher--Smith 5.1.3, 5.1.14 and 5.1.19,
printed pp.630--631,638--639,643--644.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

namespace RankOneModule

omit [Finite G] in
/-- The whole reduced subgroup is normalized by LT before any choice. -/
theorem wholeReduced_normalized : L ⊔ (T : Subgroup G) ≤
    normalizer (wholeReduced T L : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (ReducedModule J).le_normalizer_map J.subtype

omit [Finite G] in
/-- The full reduced subgroup lies in the original Sylow group. -/
theorem wholeReduced_le_sylow : wholeReduced T L ≤ (T : Subgroup G) := by
  apply (map_mono (reducedPSubgroup_le_pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))).trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right, Subgroup.pCoreIn] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- The faithful action on all of R₂(LT), through its literal centralizer quotient. -/
def wholeAction (T : Sylow 2 G) (L : Subgroup G) :=
  Representation.NormalElementaryQuotient.representation
    (ReducedModule (L ⊔ (T : Subgroup G)))
    (QuotientGroup.mk' (centralizer
      (ReducedModule (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

end RankOneModule

namespace ChosenModule
variable (D : ChosenModule T L V)
include D

/-- The original chosen orbit detects the Sylow centralizer of the entire
reduced module by inclusion, with no chosen T-invariance assumption. -/
theorem rankOne_whole_intrinsic_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
      centralizer (ReducedModule (L ⊔ (T : Subgroup G)) :
        Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le (map_subtype_le _))).trans_eq
      (D.orbit_intrinsic_centralizer h)
  · apply le_inf
    · have hh : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
        simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
          pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
      intro x hx
      exact hh (mem_map_of_mem _ hx)
    · exact le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 _)

/-- The genuine guarded numerical theorem applies to the whole reduced
action, using the actual HStar witness already present in the source. -/
theorem rankOne_whole_cubicRatio_le_two
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    cubicRatio (RankOneModule.wholeAction T L) ≤ 2 := by
  obtain ⟨hM, hTM, hLN⟩ := RankOneModule.normalizer_configuration D h
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  exact Chapter3.source_reduced_join_cubicRatio_le_two h.simpleQTKE T
    (normalizer (L : Set G)) L H h.maximal_faithful.2.1.2.1
    L.le_normalizer hLN hM (sup_le L.le_normalizer hTM) huniq hH
    (ReducedModule (L ⊔ (T : Subgroup G))) isPReduced_reducedPSubgroup
    (D.rankOne_whole_intrinsic_centralizer h)

/-- The nonfaithful residual branch has no L-fixed vector anywhere in R₂(LT). -/
theorem rankOne_whole_fixed_eq_bot_of_linear_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    RankOneModule.wholeReduced T L ⊓ centralizer (L : Set G) = ⊥ := by
  have hc := residual_centralizes_omega_of_nonfaithful h.simpleQTKE hH.1.1 hK.1 hnf
  apply Subgroup.inf_centralizer_eq_bot_of_omega_disjoint T L
    (RankOneModule.wholeReduced T L) (IsElementaryAbelian.map _)
    RankOneModule.wholeReduced_le_sylow
    (le_sup_right.trans RankOneModule.wholeReduced_normalized)
    D.sylow_normalizes_component
  exact D.centralOmega_disjoint_of_outside_centralizes h hH
    ((residual_le_omegaCentralizer_iff hH.1.1.2).mp hc)

/-- Every original choice is fixed-free, before proving its T-invariance. -/
theorem chosen_fixed_eq_bot_of_linear_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  exact le_bot_iff.mp ((inf_le_inf_right _ D.le_reduced).trans_eq
    (D.rankOne_whole_fixed_eq_bot_of_linear_source h hH hK hnf))

/-- In particular the literal layer has trivial L-centralizer. -/
theorem rankOne_layer_fixed_eq_bot_of_linear_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    RankOneModule.commutatorLayer T L ⊓ centralizer (L : Set G) = ⊥ := by
  apply le_bot_iff.mp
  apply (inf_le_inf_right _ ?_).trans_eq
    (D.rankOne_whole_fixed_eq_bot_of_linear_source h hH hK hnf)
  exact le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans RankOneModule.wholeReduced_normalized)

/-- The original exceptional exit from two independent whole-layer inputs:
a finite-copy decomposition and the bound on that very multiplicity. -/
theorem rankOne_exceptional_linear_of_bounded_copies
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    {k : ℕ} (hk : 0 < k) (hk2 : k ≤ 2)
    (hm : Chapter6.Source.IsConjugationModel L (RankOneModule.commutatorLayer T L)
      (Chapter6.Source.a5Copies k)) : RankOneModule.ExceptionalExit T L H :=
  D.rankOne_exceptional_linear_of_maximal_nonfaithful h hH hlinear hK hnf
    (Chapter6.Source.oneOrTwoA5Modules_of_copies hk hk2 hm)

end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
