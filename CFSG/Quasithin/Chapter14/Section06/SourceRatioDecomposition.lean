module
public import CFSG.Quasithin.Chapter14.Section06.SourceJhatGeneration
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Assembly
/-!
# Indecomposable actions in the original solvable plane branch

The primitive odd residual P lies in the minimum-actor subgroup K. Since
the mapped Sylow subgroup S supplements P, it also gives K = P(K ∩ S).
The original seed is fixed by S and its orbit spans U/Z. The normal odd
seed theorem therefore constructs the faithful K-action on [U/Z,P], with
the same cubic minimum and literal starred actors. P is normal abelian in
K, so the Fitting subgroup moves this whole module. Finite ratio splitting
now produces actual indecomposable factors with full Fitting movement.

The final consumer starts with an actual odd-core counterexample and
constructs its subgroup, elementary closure, quotient action and complete
decomposition. No abstract decomposition hypothesis is retained.

Source: Aschbacher--Smith, 14.6.11--12(2), printed pp.1030--1031, applying
D.2.16. Classification of the terminal factors is the subsequent D.2.17 step.
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

theorem source_solvable_minimal_ratio_decomposition
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T)) :
    ∃ f : ChapterD.RatioDecomposition.FactorData a.representation
        (ChapterD.Jhat a.representation)
        (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))),
      ∃ d : ChapterD.RatioDecomposition.Decomposition f.representation, d.FittingFull := by
  let P := pResidual 2 (J ⧸ pCore 2 J)
  let K := ChapterD.Jhat a.representation
  let S := ((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
  let Z := GenerationOne.seedSpace a (localModule T M)
  let : K.Normal := ChapterD.Jhat_normal a.representation
  obtain ⟨p,hp,hE,_hbound,_hne,_hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let : IsElementaryAbelian p P := hE
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p P).exists_card_eq
    rw [hn]
    exact (by rcases hp with rfl | rfl <;> decide : Odd p).pow
  have hPK : P ≤ K := source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hPS : P ⊔ S = ⊤ := pResidual_sup_sylow_eq_top
    ((T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
  have hKP : K = P ⊔ (K ⊓ S) := by
    apply le_antisymm
    · intro k hk
      obtain ⟨p,hp,s,hs,rfl⟩ := mem_sup_of_normal_left.mp (hPS.ge (mem_top k))
      have hsK : s ∈ K := by
        have hh := K.mul_mem (K.inv_mem (hPK hp)) hk
        simpa only [inv_mul_cancel_left] using hh
      exact mul_mem_sup hp ⟨hsK,hs⟩
    · exact sup_le hPK inf_le_left
  have hZ : Z ≤ fixedSpace a.representation S :=
    source_rankTwo_seed_fixed hG T hempty hM hu hmany hcard e hab J hJ.1 a
  have hgen : Submodule.span (ZMod 2)
      {w | ∃ g v, v ∈ Z ∧ a.representation g v = w} = ⊤ := by
    apply top_unique
    rw [← GenerationOne.seedSpace_iSup_maps_eq_top a]
    apply iSup_le
    intro g v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact Submodule.subset_span ⟨g,w,hw,rfl⟩
  have hratio : cubicRatio a.representation ≤ 2 := (cubicRatio_le_quadraticRatio _).trans
    (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  let f := ChapterD.RatioDecomposition.normalOddFactorData a.representation a.faithful
    K P S hodd hKP Z hZ hgen rfl ((ChapterD.QhatStar_nonempty_iff _).mpr hratio)
  have hPF : P.subgroupOf K ≤ fittingSubgroup K :=
    le_sSup ⟨inferInstance,inferInstance⟩
  have hfull : subspaceCommutator f.representation ⊤ (fittingSubgroup K) = ⊤ :=
    ChapterD.RatioDecomposition.oddMovedAction_full_of_le a.representation K P hPK hodd _ hPF
  exact ⟨f,ChapterD.RatioDecomposition.source_fitting_decomposition f.representation
    f.faithful f.generated hfull (f.ratio ▸ hratio)⟩

/-- An actual odd-core counterexample supplies all action and decomposition data. -/
theorem source_oddCore_counterexample_decomposition
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (_hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ _hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J),
      ∃ a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T),
      ∃ f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))),
        ∃ d : ChapterD.RatioDecomposition.Decomposition f.representation, d.FittingFull := by
  obtain ⟨J,hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  obtain ⟨hU,a,_hq⟩ := source_rankTwo_quadratic_bound
    hG T hempty hM hu hmany hcard e hab J hJ.1
  let := hU
  exact ⟨J,hJ,hJH,hs,hU,a,source_solvable_minimal_ratio_decomposition
    hG T hempty hM hu hmany hcard e hab J hJ hs a⟩

end CFSG.Quasithin.Chapter14.Section06
