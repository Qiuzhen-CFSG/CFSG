module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCubicGeometry
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The faithful cubic action quotient and its solvable kernel

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the nonnormalizing residual images
force each original vertex to meet C_D(W) in exactly O₂(D). The common
Sylow intersection and the odd-order theorem make C_D(W) solvable.

The two vertex images have common Sylow subgroups of index three.
They cannot coincide, since their residual images do not normalize one
another. Thus D/C_D(W) is a Goldschmidt triple with the full original
overlap and trivial two-core. The first isomorphism theorem identifies
its amalgam with the original three quotients by O₂(D), compatibly with
both inclusions. The order-four chief interval supplies every premise.

This establishes the kernel reduction used at the beginning of 14.5.8;
solvability of the entire D and the later containment argument remain.
Source: Aschbacher–Smith, F.6.7–8, printed p.305; 14.5.6–8,
printed pp.1014–1015; 14.7.20, printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u

private theorem action_kernel_intersections
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (C : Subgroup D) [C.Normal] (hQC : pCore 2 D ≤ C)
    (hout : ¬ ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 A).map A.subtype).map (QuotientGroup.mk' C) : Set _)) :
    A ⊓ C = pCore 2 D ∧ B ⊓ C = pCore 2 D ∧ Group.IsSolvable C := by
  let q := QuotientGroup.mk' C
  have hAC : A ⊓ C ≤ (pCore 2 A).map A.subtype := by
    apply (ht.left_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr
    intro hle
    have hz : ((pResidual 2 A).map A.subtype).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hle)
    apply hout
    rw [hz,normalizer_eq_top]
    exact le_top
  have hBC : B ⊓ C ≤ (pCore 2 B).map B.subtype := by
    apply (ht.right_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr
    intro hle
    have hz : ((pResidual 2 B).map B.subtype).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hle)
    apply hout
    rw [hz]
    exact bot_le
  have hTC : (A ⊓ B) ⊓ C = pCore 2 D := le_antisymm
    (ht.normal_intersection_le_twoCore C hAC hBC)
    (le_inf ht.twoCore_isGreatest.1.1 hQC)
  have hA := ht.left_intersection_eq_core_intersection C hAC
  have hB := ht.symm.left_intersection_eq_core_intersection C hBC
  have hsol : Group.IsSolvable (C ⧸ (pCore 2 D).subgroupOf C) := by
    have hh := ht.normal_quotient_solvable C hAC hBC
    rwa [sup_eq_left.mpr hQC] at hh
  let : Group.IsNilpotent ((pCore 2 D).subgroupOf C) :=
    (pCore_isPGroup (p := 2) (G := D)).comap_subtype.isNilpotent
  exact ⟨hA.1.trans (hA.2.trans hTC),
    hB.1.trans (hB.2.trans (by simpa only [inf_comm B A] using hTC)),
    (Group.isSolvable_iff_subgroup_quotient ((pCore 2 D).subgroupOf C)).mpr
      ⟨inferInstance,hsol⟩⟩

private def action_local_quotient_equiv
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    (f : D →* E) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    (D ⧸ pCore 2 D) ≃* (E ⧸ pCore 2 E) := by
  let q := (QuotientGroup.mk' (pCore 2 E)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have he : q.ker = pCore 2 D := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

private theorem action_intermediate {D : Type*} [Group D] {A B C : Subgroup D}
    (hAB : A ≤ B) (hBC : B ≤ C) (hi : A.relIndex C = 3) : B = A ∨ B = C := by
  have hm := relIndex_mul_relIndex A B C hAB hBC
  rw [hi] at hm
  have hp : (A.relIndex B * B.relIndex C).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hB⟩ | ⟨_,hA⟩
  · exact Or.inr (le_antisymm hBC (relIndex_eq_one.mp hB))
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hA) hAB)

private theorem action_quotient_triple
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (C : Subgroup D) [C.Normal] (hQC : pCore 2 D ≤ C)
    (hout : ¬ ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 A).map A.subtype).map (QuotientGroup.mk' C) : Set _)) :
    let q := QuotientGroup.mk' C
    A.map q ⊓ B.map q = (A ⊓ B).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) := by
  let q := QuotientGroup.mk' C
  obtain ⟨hAC,hBC,_⟩ := action_kernel_intersections ht C hQC hout
  have hlocal (J : Subgroup D) (hj : J ⊓ C = pCore 2 D)
      (e : Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((J.map q) ⧸ pCore 2 (J.map q)) ≃* Equiv.Perm (Fin 3)) := by
    have hk : IsPGroup 2 (q.subgroupMap J).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      have he : C.subgroupOf J = (pCore 2 D).subgroupOf J := by
        ext x
        change (x : D) ∈ C ↔ (x : D) ∈ pCore 2 D
        rw [←hj]
        exact (and_iff_right x.property).symm
      rw [he]
      exact pCore_isPGroup.comap_subtype
    exact ⟨(action_local_quotient_equiv _ (q.subgroupMap_surjective J) hk).symm.trans e.some⟩
  have hA := hlocal A hAC ht.quotient_left
  have hB := hlocal B hBC ht.quotient_right
  obtain ⟨T,hT⟩ := ht.intersection_sylow
  let S := T.mapSurjective (QuotientGroup.mk'_surjective C)
  have hS : (S : Subgroup _) = (A ⊓ B).map q := by
    change (T : Subgroup D).map q = _
    rw [hT]
  have hSA : (S : Subgroup _) ≤ A.map q := hS ▸ map_mono inf_le_left
  have hSB : (S : Subgroup _) ≤ B.map q := hS ▸ map_mono inf_le_right
  have hAi : (S : Subgroup _).relIndex (A.map q) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three hA.some (S.subtype hSA)
  have hBi : (S : Subgroup _).relIndex (B.map q) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three hB.some (S.subtype hSB)
  have hi : A.map q ⊓ B.map q = (A ⊓ B).map q := by
    rcases action_intermediate (le_inf hSA hSB) inf_le_left hAi with hI | heA
    · exact hI.trans hS
    rcases action_intermediate (le_inf hSA hSB) inf_le_right hBi with hI | heB
    · exact hI.trans hS
    have he : A.map q = B.map q := heA.symm.trans heB
    apply False.elim
    apply hout
    rw [map_embedded_pResidual,map_embedded_pResidual,he]
    exact ((pResidual 2 (B.map q)).map (B.map q).subtype).le_normalizer
  refine ⟨hi,?_,hA,hB,S,?_⟩
  · rw [←Subgroup.map_sup,ht.generated,map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  · exact hi.trans hS.symm

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The intrinsic residuals of the two original vertices, in the generated
group, are exactly the restrictions of L₂ and Y. -/
theorem cubic_action_residuals
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    (pResidual 2 A).map A.subtype = (F.Li L 2).subgroupOf D ∧
      (pResidual 2 B).map B.subtype = Y.subgroupOf D := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hPD : F.P L ≤ D := le_sup_left
  have hBD : Y ⊔ (T : Subgroup G) ≤ D := le_sup_right
  have hYD : Y ≤ D := le_sup_left.trans hBD
  have hXD : F.Li L 2 ≤ D := by
    apply le_trans _ hPD
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left
  constructor
  · apply (map_injective D.subtype_injective)
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPD,
      plane_parabolic_residual h structural,map_subgroupOf_eq_of_le hXD]
  · apply (map_injective D.subtype_injective)
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hBD,
      embedded_pResidual_join_pGroup Y _ hYp T.isPGroup' hYT,
      map_subgroupOf_eq_of_le hYD]

/-- Both original vertices meet the point-span centralizer in exactly O₂(D).
The centralizer is solvable, as required in the first step of 14.5.8. -/
theorem cubic_generated_action_kernel_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let C := centralizer (W.subgroupOf D : Set D)
    (F.P L).subgroupOf D ⊓ C = pCore 2 D ∧
      (Y ⊔ (T : Subgroup G)).subgroupOf D ⊓ C = pCore 2 D ∧
      Group.IsSolvable C := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  have hWC := (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.2.2
  have hQC : pCore 2 D ≤ centralizer (W.subgroupOf D : Set D) := by
    intro x hx w hw
    apply Subtype.ext
    exact (le_centralizer_iff.mp hWC) (mem_map_of_mem D.subtype hx) w hw
  apply action_kernel_intersections (cubic_goldschmidt_triple h structural Y hYH he)
    _ hQC
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [hr.1,hr.2]
  exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout

/-- The original full point-normality interface. -/
theorem cubic_generated_action_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let C := centralizer (W.subgroupOf D : Set D)
    (F.P L).subgroupOf D ⊓ C = pCore 2 D ∧
      (Y ⊔ (T : Subgroup G)).subgroupOf D ⊓ C = pCore 2 D ∧
      Group.IsSolvable C := by
  apply cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The literal conjugation quotient retains the full original overlap and
is a Goldschmidt triple with trivial two-core. The nonnormalizing residual
images rule out collapse of its two vertices. -/
theorem cubic_generated_action_triple_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ((F.P L).subgroupOf D).map q ⊓ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q =
        ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D |>.map q)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D |>.map q) ∧
      pCore 2 (D ⧸ C) = ⊥ := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  have hQC : pCore 2 D ≤ C := by
    intro x hx
    have hh := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous
      Y hYH hYL hYp hYT hout he).1
    rw [←hh] at hx
    exact hx.2
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have ho : ¬ ((pResidual 2 ((Y ⊔ (T : Subgroup G)).subgroupOf D)).map
      ((Y ⊔ (T : Subgroup G)).subgroupOf D).subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 ((F.P L).subgroupOf D)).map
        ((F.P L).subgroupOf D).subtype).map (QuotientGroup.mk' C) : Set _) := by
    rw [hr.1,hr.2]
    exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
  obtain ⟨hi,ht⟩ := action_quotient_triple
    (cubic_goldschmidt_triple h structural Y hYH he) C hQC ho
  have hinter : (F.P L).subgroupOf D ⊓ (Y ⊔ (T : Subgroup G)).subgroupOf D =
      (T : Subgroup G).subgroupOf D := by
    apply le_antisymm
    · intro x hx
      have hh : (x : G) ∈ F.P L ⊓ F.H :=
        ⟨hx.1,(sup_le hYH (F.invariant 1)) hx.2⟩
      rwa [plane_parabolic_inf_point h structural] at hh
    · intro x hx
      exact ⟨F.binary_sylow_le_P L hx,
        (le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hx⟩
  rw [hinter] at hi
  exact ⟨hi,ht,(cubic_generated_span_reduced h hab structural previous Y hYH he).quotient_pCore_eq_bot⟩

private def action_kernel_equiv
    {D : Type*} [Group D] [Finite D] (C : Subgroup D) [C.Normal]
    (J : Subgroup D) (hj : J ⊓ C = pCore 2 D) :
    (J ⧸ (QuotientGroup.mk' (pCore 2 D)).ker.subgroupOf J) ≃*
      J.map (QuotientGroup.mk' C) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',QuotientGroup.ker_mk']
    ext x
    change (x : D) ∈ pCore 2 D ↔ (x : D) ∈ C
    rw [←hj]
    exact and_iff_right x.property)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk' C).subgroupMap_surjective J))

/-- The original full point-normality interface. -/
theorem cubic_generated_action_triple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ((F.P L).subgroupOf D).map q ⊓ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q =
        ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D |>.map q)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D |>.map q) ∧
      pCore 2 (D ⧸ C) = ⊥ := by
  apply cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The action amalgam is compatibly isomorphic to the original three
quotients by O₂(D). Both inclusion squares use the actual quotient maps. -/
def cubicActionAmalgamIsoOfNormalizesPoint
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    Theory.GroupTheory.RankTwoAmalgam.Iso
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroupQuotients
        (QuotientGroup.mk' (pCore 2 D)) A (A ⊓ B) B inf_le_left inf_le_right)
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups
        (A.map q) ((A ⊓ B).map q) (B.map q)
        (map_mono inf_le_left) (map_mono inf_le_right)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  obtain ⟨hAC,hBC,_⟩ := cubic_generated_action_kernel_of_normalizes_point h hab structural previous
    Y hYH hYL hYp hYT hout he
  have hTC : (A ⊓ B) ⊓ C = pCore 2 D := by
    apply le_antisymm ((inf_le_inf inf_le_left le_rfl).trans_eq hAC)
    exact le_inf (cubic_goldschmidt_triple h structural Y hYH he).twoCore_isGreatest.1.1
      (hAC ▸ (inf_le_right : A ⊓ C ≤ C))
  exact {
    left := action_kernel_equiv C A hAC
    middle := action_kernel_equiv C (A ⊓ B) hTC
    right := action_kernel_equiv C B hBC
    left_commutes := fun b => by
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ b
      rfl
    right_commutes := fun b => by
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ b
      rfl }

/-- The original full point-normality interface. -/
def cubicActionAmalgamIso
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    Theory.GroupTheory.RankTwoAmalgam.Iso
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroupQuotients
        (QuotientGroup.mk' (pCore 2 D)) A (A ⊓ B) B inf_le_left inf_le_right)
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups
        (A.map q) ((A ⊓ B).map q) (B.map q)
        (map_mono inf_le_left) (map_mono inf_le_right)) := by
  apply cubicActionAmalgamIsoOfNormalizesPoint h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement in
/-- The actual order-four chief interval supplies a faithful Goldschmidt
action quotient and its solvable kernel. All earlier point-normality and
cubic-quotient premises are discharged from the original extraspecial branch. -/
theorem extraspecial_four_interval_cubic_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let A := (F.P L).subgroupOf D
      let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      A ⊓ C = pCore 2 D ∧ B ⊓ C = pCore 2 D ∧ Group.IsSolvable C ∧
      A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧ pCore 2 (D ⧸ C) = ⊥ ∧
      Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (Theory.GroupTheory.RankTwoAmalgam.ofSubgroupQuotients
          (QuotientGroup.mk' (pCore 2 D)) A (A ⊓ B) B inf_le_left inf_le_right)
        (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups
          (A.map q) ((A ⊓ B).map q) (B.map q)
          (map_mono inf_le_left) (map_mono inf_le_right))) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨hAC,hBC,hsol⟩ := cubic_generated_action_kernel h hab structural previous hn
    Y hYH hYp hYT hout he
  obtain ⟨hi,ht,hcore⟩ := cubic_generated_action_triple h hab structural previous hn
    Y hYH hYp hYT hout he
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hAC,hBC,hsol,hi,ht,hcore,
    ⟨cubicActionAmalgamIso h hab structural previous hn Y hYH hYp hYT hout he⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
