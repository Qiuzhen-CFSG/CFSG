module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.CartanRankOne
public import Theory.GroupTheory.PerfectSmallTwoAction

/-!
# The original line-normalizer reduction for Cartan normalization

The old residual, once it normalizes the literal tensor line, lies in a
unique normal C-component of that line normalizer. The component is perfect,
so it centralizes the four-group. Its two-core lies in the original Sylow
subgroup, and its intersection with the actual Cartan is exactly the marked
order-three subgroup. These conclusions use the genuine source containment
and normality theorem 1.2.4, with the original local A₅ quotient retained.

Equality with the old residual gives Cartan normalization. The established
rank-one action theorem also gives normalization when the component quotient
is centerless with two-group outer automorphisms. Thus any remaining case
has a proper containing component and fails precisely those rank-one inputs.
The last theorem constructs this reduction from the completed nonzero-core
branch of 9.3.1. The containing-component model sieve remains independent;
this module does not assert the full Cartan-normalization conclusion.

Source: Aschbacher--Smith, Proposition 9.3.1, first two reductions,
printed p.732 of the combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Construct the actual normal container inside the original line normalizer,
including its centralization, core placement and marked Cartan intersection. -/
theorem old_residual_line_normalizer_container
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hKU : (pResidual 2 H).map H.subtype ≤ normalizer (m.tensorLine : Set G)) :
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype ≤ J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 := by
  let N := normalizer (m.tensorLine : Set G)
  let K := (pResidual 2 H).map H.subtype
  have hKN : K ≤ N := hKU
  let P := T.subtype m.tensorLine_normalized
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  have hq : IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hN.stronglyQuasithin p hp ho)
  have hKl : K.subgroupOf N ∈ Chapter1.L N (P : Subgroup N) :=
    (Chapter1.mem_LIn_iff_subgroupOf m.tensorLine_normalized hKU).mp
      ⟨hKU,source_hstar_residual_mem_local_of_a5 hH eK⟩
  have hPK : (P : Subgroup N) ≤ normalizer (K.subgroupOf N : Set N) := by
    rw [←subgroupOf_normalizer_eq hKU]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  obtain ⟨I,⟨hI,hKI,hnI⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hq P hKl hPK
  let J := I.map N.subtype
  have hJN : J ≤ N := map_subtype_le I
  have hIJ : J.subgroupOf N = I := by
    exact comap_map_eq_self_of_injective N.subtype_injective I
  have hJ : (J.subgroupOf N).IsCComponent := hIJ ▸ hI
  have hnJ : (J.subgroupOf N).Normal := hIJ ▸ hnI
  have hKJ : K ≤ J := by
    simpa only [map_subgroupOf_eq_of_le hKN] using map_mono (f := N.subtype) hKI
  have hAJ : A ≤ normalizer (J : Set G) := hAU.trans
    ((normal_subgroupOf_iff_le_normalizer hJN).mp hnJ)
  have hUC : J ≤ centralizer (m.tensorLine : Set G) := by
    let := hI.perfect
    let U := m.tensorLine.subgroupOf N
    let : U.Normal := normal_subgroupOf_of_le_normalizer le_rfl
    have hU : Nat.card U ≤ 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe m.tensorLine.le_normalizer).toEquiv]
      exact m.card_tensorLine.le
    have hc := le_centralizer_of_isPerfect_of_card_le_four I U hU
    rintro _ ⟨j,hj,rfl⟩ u hu
    exact congrArg Subtype.val (hc hj ⟨u,m.tensorLine.le_normalizer hu⟩ hu)
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := map_mono (f := N.subtype) (pCoreIn_le_of_subnormal 2 hI.subnormal)
    rw [map_pCoreIn_of_injective 2 _ N.subtype N.subtype_injective] at hh
    exact hh.trans ((pCoreIn_le_sylow N P).trans_eq
      (map_subgroupOf_eq_of_le m.tensorLine_normalized))
  have hAJB : A ⊓ J = B := by
    apply le_antisymm
    · rw [hBC]
      exact inf_le_inf_left A hUC
    · exact le_inf (hBC ▸ inf_le_left) (hBK.trans hKJ)
  have hr : primeRank 3 J ≤ 2 := by
    have hi := primeRank_subgroup_le 3 (J.subgroupOf N)
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hJN)] at hi
    exact hi.trans (hN.stronglyQuasithin 3 (by decide) (by decide))
  exact ⟨J,hJN,hJ,hnJ,hKJ,hAJ,hUC,hQT,hAJB,hr⟩

/-- A failure of Cartan normalization leaves a proper original container
outside the already proved centerless rank-one outer-two-group case. -/
theorem old_residual_cartan_normalization_reduction
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) [IsElementaryAbelian 3 A]
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hKU : (pResidual 2 H).map H.subtype ≤ normalizer (m.tensorLine : Set G)) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      ¬ (primeRank 3 J ≤ 1 ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
        IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J))) := by
  by_cases hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)
  · exact Or.inl hAK
  obtain ⟨J,hJN,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr⟩ :=
    m.old_residual_line_normalizer_container hH eK A B hAU hBK hBC hKU
  have hp : (pResidual 2 H).map H.subtype < J := hKJ.lt_of_ne (by
    intro he
    exact hAK (he ▸ hAJ))
  refine Or.inr ⟨J,hJN,hJ,hnJ,hp,hAJ,hJC,hQT,hAJB,hr,?_⟩
  rintro ⟨hr1,hz,hout⟩
  exact hAK (m.cartan_normalizes_old_residual_of_rank_one hH eK A B J
    hJN hJ hKJ (hBC ▸ inf_le_left) hBK hB3 hAU hr1 hz hout)

/-- The completed nonzero-core line theorem supplies the entire line-normalizer
input of the original Cartan reduction, with the same H, A, B and residual. -/
theorem nonzero_core_cartan_normalization_reduction
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      ¬ (primeRank 3 J ≤ 1 ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
        IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J))) := by
  let := hAe
  have hKC := m.old_residual_centralizes_tensorLine_of_nonzero_cartan_core
    hH eK A B hAB hA9 hAe hB3 hBC hcore
  exact m.old_residual_cartan_normalization_reduction hH eK A B
    (hAB.trans m.borel_normalizes_tensorLine) hBK hB3 hBC
    (hKC.trans (Subgroup.centralizer_le_normalizer _))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
