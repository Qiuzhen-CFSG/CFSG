module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelIntersection
public import Theory.SpecificGroups.SymmetricEight.DoubleSylow
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier

/-!
# Completion of the common-centralizer calculation in 12.2.25

The remaining dimension-four obstruction is a central double cover of A₈.
If the two Sylow factors meet, the order-two bound puts all of T in L.
In L/V the image of the original U is a normal subgroup of the image Sylow,
and the literal action-kernel equality makes it disjoint from the covering
kernel. The double-cover Sylow theorem kills this image, contradicting the
given orders of U and U∩V. Thus the Sylow factors are disjoint in dimension
four as well as in the already established dimensions three and five.

The final constructor proves every field of LocalRigidityCentralizers from
the original source data. In particular no kernel split, Sylow disjointness
or residual-normalization premise remains. Structural1222 is the permitted
earlier-source input; its eventual discharge and the later rigidity/parabolic
argument belong to qt-d-12213-local-rigidity. The final application discharges
the common-centralizer premise of the existing higher-dimensional action
consumer, retaining that consumer's later residual-normality and fixed-space
premises with the same assembly owner.

Source: Aschbacher--Smith, original 12.2.25, printed pp.804--805,
through Y ≤ N_G(C_T(U)); the central-cover calculation uses the actual
PSL₄(2) ≃ A₈ equivalence and the checked Schur cover.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

private theorem sylow_le_component_of_intersection_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hne : ((T : Subgroup G) ⊓ L) ⊓
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) ≠ ⊥) : (T : Subgroup G) ≤ L := by
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let B := ((T : Subgroup G) ⊓ L) ⊓ Z
  have hlo : 1 < Nat.card B := (Subgroup.one_lt_card_iff_ne_bot (H := B)).mpr hne
  have hhi : Nat.card Z ≤ 2 := source_component_centralizer_card h D structural A C hnone
  have he : B = Z := eq_of_le_of_card_ge inf_le_right (by omega)
  have hZL : Z ≤ L := he ▸ (inf_le_left.trans inf_le_right : B ≤ L)
  rw [source_sylow_split h D structural A C hnone]
  exact sup_le inf_le_right hZL

open scoped MatrixGroups
open GLS3.Chapter5.SchurPresentation

/-- The dimension-four Sylow factors are disjoint, using the literal image of U. -/
theorem four_sylow_disjoint
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 4) :
    Disjoint ((T : Subgroup G) ⊓ L)
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  subst d
  by_contra hn
  have hne := mt disjoint_iff.mpr hn
  have hTL := sylow_le_component_of_intersection_ne_bot h D structural A C hnone hne
  have hUL : U ≤ L := C.core_le_sylow.trans hTL
  let := h.quasisimple
  let q := ChapterC.blockCoreProjection (L := L)
  let r := QuotientGroup.mk' (ChapterC.blockU L)
  have hq : Function.Surjective q := ChapterC.blockCoreProjection_surjective
  have hqc : q.ker ≤ center (L ⧸ ChapterC.blockU L) := by
    rw [ChapterC.blockCoreProjection_ker]
    exact ChapterC.blockU_core_image_le_center
  have hqp : IsPGroup 2 q.ker := by
    rw [ChapterC.blockCoreProjection_ker]
    exact pCore_isPGroup.map _
  let : Group.IsPerfect (L ⧸ ChapterC.blockU L) :=
    IsPPerfect.isPerfect_of_surjective_pGroup_kernel
      (C.block.2.1.quotient_twoPerfect _) q hq hqp
  let : IsQuasisimple (L ⧸ ChapterC.blockU L) :=
    PerfectCentralCovering.Cover.isQuasisimple
      { toMonoidHom := q, surjective := hq, ker_le_center := hqc, isPerfect := inferInstance }
  let e := A.natural.choose.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  let : IsQuasisimple (alternatingGroup (Fin 8)) := alternatingGroup_isQuasisimple 3
  let f : Covering (L ⧸ ChapterC.blockU L) (alternatingGroup (Fin 8)) :=
    { toMonoidHom := e.toMonoidHom.comp q
      surjective := e.surjective.comp hq }
  have hk : f.toMonoidHom.ker = q.ker := MonoidHom.ker_comp_of_injective _ _ e.injective
  have hkne : f.toMonoidHom.ker ≠ ⊥ := by
    intro he
    have hi : Function.Injective q := (MonoidHom.ker_eq_bot_iff _).mp (hk ▸ he)
    exact hn (sylow_disjoint_of_component_core D A (core_eq_of_blockProjection_injective D A C hi))
  have hkcard : Nat.card f.toMonoidHom.ker = 2 := by
    have hdvd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
      (schurAlternatingCovering 3) (theorem_5_2_3_b_universality 3 (by decide) (by decide)) f
    rw [natCard_ker_schurAlternatingCovering] at hdvd
    have hlt := (Subgroup.one_lt_card_iff_ne_bot (H := f.toMonoidHom.ker)).mpr hkne
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    omega
  let t := T.subtype hTL
  let S := t.mapSurjective (QuotientGroup.mk'_surjective (ChapterC.blockU L))
  let B := (U.subgroupOf L).map r
  have hBS : B ≤ (S : Subgroup (L ⧸ ChapterC.blockU L)) :=
    map_mono (fun _ hu => C.core_le_sylow hu)
  have hSnorm : (S : Subgroup (L ⧸ ChapterC.blockU L)) ≤ normalizer (B : Set _) := by
    apply le_trans (map_mono (show (t : Subgroup L) ≤ normalizer (U.subgroupOf L : Set L) from ?_))
      (Subgroup.le_normalizer_map r)
    intro l hl
    exact Subgroup.le_normalizer_comap L.subtype (C.sylow_normalizes_core hl)
  have hBdis : Disjoint B f.toMonoidHom.ker := by
    apply disjoint_def.mpr
    rintro x ⟨l,hl,rfl⟩ hx
    have hqr : q (r l) = 1 := by
      apply e.injective
      exact hx.trans e.map_one.symm
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp (by
      simpa only [q, r, ChapterC.blockCoreProjection, QuotientGroup.mk'_apply,
        QuotientGroup.lift_mk] using hqr)
    have hlV : (l : G) ∈ V := (C.action_kernel.le ⟨hl, D.core_centralizes
      ((pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
        (mem_map_of_mem L.subtype hlcore))⟩).2
    have hlblock : l ∈ ChapterC.blockU L := by
      have hh := LiteralNaturalBlock.blockLayer_eq D A C
      rw [← hh] at hlV
      obtain ⟨l',hl',he⟩ := hlV
      exact Subtype.coe_injective he ▸ hl'
    exact (QuotientGroup.eq_one_iff l).mpr hlblock
  let N := B.subgroupOf (S : Subgroup (L ⧸ ChapterC.blockU L))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hBS).mpr hSnorm
  have hN : N = ⊥ := Theory.SpecificGroups.SymmetricEight.DoubleSylow.normal_subgroup_eq_bot
    f hkcard S N (by rw [map_subgroupOf_eq_of_le hBS]; exact hBdis)
  have hB : B = ⊥ := by
    rw [← map_subgroupOf_eq_of_le hBS]
    change B.subgroupOf (S : Subgroup (L ⧸ ChapterC.blockU L)) = ⊥ at hN
    rw [hN, Subgroup.map_bot]
  have hUV : U ≤ V := by
    intro u hu
    let l : L := ⟨u,hUL hu⟩
    have hr : r l = 1 := by
      have hm : r l ∈ B := mem_map_of_mem r hu
      rwa [hB, mem_bot] at hm
    have hl := (QuotientGroup.eq_one_iff l).mp hr
    rw [← LiteralNaturalBlock.blockLayer_eq D A C]
    exact mem_map_of_mem L.subtype hl
  have hc := C.hyperplane
  rw [inf_eq_left.mpr hUV,C.dimension] at hc
  norm_num at hc

/-- The complete common-centralizer record in dimension four. -/
theorem four_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 4) : LocalRigidityCentralizers T L V U P :=
  centralizers_of_sylow_disjoint h D structural A C hnone
    (four_sylow_disjoint h D structural A C hnone hd)

/-- Both higher-dimensional branches, with every centralizer field discharged. -/
theorem higher_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 4 ∨ d = 5) : LocalRigidityCentralizers T L V U P := by
  rcases hd with hd | hd
  · exact four_centralizers h D structural A C hnone hd
  · exact five_centralizers h D structural A C hnone hd

/-- The complete common-centralizer and residual-normalizer calculation from
the original source hypotheses, in all three permitted dimensions. -/
theorem source_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) : LocalRigidityCentralizers T L V U P := by
  by_cases hd : d = 3
  · exact three_centralizers h D structural A C hnone hd
  · exact higher_centralizers h D structural A C hnone (by have := A.dimension; omega)

/-- Application to the actual higher-dimensional quotient and conjugation action.
The later residual-normality and fixed-space premises retain their original
assembly owner, qt-d-12213-local-rigidity. -/
theorem source_higher_normalizer_action_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G))
    (hf : ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (rigidityHyperplaneResidual L U V : Set G) =
        (T : Subgroup G) ⊓ centralizer (L : Set G)) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ∃ a : HigherRigidity.NormalizerQuotient U →* MulAut U,
        Function.Injective a ∧ ∀ (g : normalizer (U : Set G)) (u : U),
          (a (HigherRigidity.quotient U g) u : G) = (g : G) * (u : G) * (g : G)⁻¹ :=
  higher_normalizer_action_of_residual_normal h D structural A C
    (source_centralizers h D structural A C hnone) hn hf

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
