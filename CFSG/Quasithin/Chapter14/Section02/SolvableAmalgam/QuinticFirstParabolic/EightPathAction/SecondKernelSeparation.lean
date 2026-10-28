module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.SecondKernel
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.CentralKernel

public import Theory.GroupAction.RankTwoCosetGeometry.NeighborKernelSeparation

/-!
# Separating the original quintic second kernels

Let C=C_H(⟨Vᴴ⟩), the literal second-ball kernel at H. Its normalizer
inside the cubic parabolic X is exactly T: T normalizes C, and any larger
normalizer is all of X since |X:T|=3. That would make the nontrivial C
normal in both parabolics, contrary to the trivial common core.

Transport through the actual coset maps therefore separates the second
kernels at distinct quintic neighbors of every cubic vertex. Both original
quotient alternatives are retained. The six-path consumer in
`EightPathAction` uses this separation at its two interior quintic vertices;
the longer path extensions remain with qt-e-quintic-sylow-lower.

Source: Aschbacher--Smith F.7.3, pp.311--312;14.2.6 and14.2.20--21,
pp.982,988--989. No model identification or stabilizer-order premise is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open ChapterF.Section07 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The original span centralizer has precisely T as normalizer inside X. -/
theorem source_quintic_span_centralizer_cubic_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let C := H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)
    X ⊓ normalizer (C : Set G) = (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (U : Set G)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hCH : C ≤ H := inf_le_left
  have hCK : C ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 := by
    change H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) ≤ _
    rw [←source_quintic_crossing_core_normalCore hG T hempty hM hu hmany hcard e H hH]
    exact (map_mono (f := H.subtype)
      ((H.pCoreIn 2 ⊓ X.pCoreIn 2).subgroupOf H).normalCore_le).trans (by
        rw [map_subgroupOf_eq_of_le (inf_le_left.trans (pCoreIn_le 2 H))])
  have hCX : C ≤ X := (hCK.trans inf_le_right).trans (pCoreIn_le 2 X)
  have hnH : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  have hne : C ≠ ⊥ := by
    intro hc
    have hV : localModule T M ≤ C := by
      obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
      let := he
      obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
      have hUQ : U ≤ H.pCoreIn 2 := by
        have hh := hl.U_le_core
        change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
        simpa only [rankTwoSeed_eq_localModule] using hh
      let : IsElementaryAbelian 2 U :=
        (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
      exact (le_conjugateSpanBy _ _).trans
        (le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U))
    have hVbot := bot_unique (hc ▸ hV)
    rw [hVbot,card_bot] at hcard
    omega
  have hnot : ¬ X ≤ normalizer (C : Set G) := by
    intro hnX
    have hsmall := source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi
    have hF := (source_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e H hH
      (hsmall.elim Or.inl (Or.inr ∘ Or.inl))).1
    exact hne (AmalgamLocalCores.common_normal_eq_bot H X C
      (le_inf hCH hCX) hnH hnX
      (source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2)
      (hF.local_core_selfCentralizing 0))
  obtain ⟨_,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hiX : (T : Subgroup G).relIndex X = 3 :=
    SymmetricThreeTwoCore.sylow_index_three eX (T.subtype hTX)
  have hTN : (T : Subgroup G) ≤ X ⊓ normalizer (C : Set G) := le_inf hTX (hTH.trans hnH)
  apply le_antisymm ?_ hTN
  have hm := relIndex_mul_relIndex (T : Subgroup G) (X ⊓ normalizer (C : Set G)) X hTN inf_le_left
  rw [hiX] at hm
  rcases Nat.prime_mul_iff.mp (hm ▸ (by decide : Nat.Prime 3)) with hp | hp
  · exact (hnot ((relIndex_eq_one.mp hp.2).trans inf_le_right)).elim
  · exact relIndex_eq_one.mp hp.2

/-- The quintic second kernel has exactly the original edge group as cubic normalizer. -/
theorem source_quintic_second_kernel_cubic_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    F false ⊓ normalizer (ballKernel F (base F true) 2 : Set (X ⊔ H : Subgroup G)) =
      F false ⊓ F true := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F := Geometry.family X H
  let C := H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)
  have hCL : C ≤ L := inf_le_left.trans le_sup_right
  have hK : ballKernel F (base F true) 2 = C.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [source_quintic_second_ball_kernel hG T hempty hM hu hmany hcard e H hH hi,
      map_subgroupOf_eq_of_le hCL]
  obtain ⟨_,_,hmap⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  change F false ⊓ normalizer (ballKernel F (base F true) 2 : Set L) = F false ⊓ F true
  rw [hK,←subgroupOf_normalizer_eq hCL]
  apply map_injective L.subtype_injective
  change ((X ⊓ normalizer (C : Set G)).subgroupOf L).map L.subtype = _
  rw [map_subgroupOf_eq_of_le
    (show X ⊓ normalizer (C : Set G) ≤ L from inf_le_left.trans le_sup_left),
    source_quintic_span_centralizer_cubic_normalizer hG T hempty hM hu hmany hcard e H hH hi,hmap]

/-- The second kernels at distinct quintic neighbors of a cubic vertex are distinct. -/
theorem source_quintic_second_kernel_separation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ u w v : Vertex F, u.type = true → (graph F).Adj u w →
      (graph F).Adj w v → u ≠ v → ballKernel F u 2 ≠ ballKernel F v 2 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have hn := source_quintic_second_kernel_cubic_normalizer
    hG T hempty hM hu hmany hcard e H hH hi
  exact fun _ _ _ hu huw hwv huv =>
    neighbor_ballKernel_ne_of_normalizer F 2 hn hu huw hwv huv

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
