module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.CheckedShortAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import Theory.GroupTheory.SylowKernelCore

/-!
# The elementary layer for the six-point replacement

The literal residual lift of the six-point stabilizer has its two-core
inside the original two-core. Its core commutator therefore lies in the
original ordinary A₇ module. Sylow averaging on that elementary layer
centralizes the source point once its local and replacement fixed spaces
agree; no block recognition of the replacement is required.

Source: Aschbacher–Smith, Lemma 13.6.22, printed pp.932–933.
-/

public section
open Subgroup CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open BinaryRankTwo AlternatingBranches.OrdinarySeven
variable {G : Type*} [Group G] [Finite G]

/-- The exact residual-lift kernel puts its two-core in the original core. -/
theorem replacement_core_le (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) :
    (replacement K e x).pCoreIn 2 ≤ K.pCoreIn 2 := by
  rw [replacement, ← map_pCoreIn_of_injective 2 _ K.subtype K.subtype_injective]
  apply map_mono
  change (pCore 2 (residualLift (blockProjection K e) x)).map
    (residualLift (blockProjection K e) x).subtype ≤ pCore 2 K
  rw [← liftProjection_kernel_eq_core (blockProjection K e)
    (blockProjection_surjective K e)
    (by rw [blockProjection_kernel]; exact pCore_isPGroup) x,
    liftProjection_kernel, blockProjection_kernel]
  exact map_comap_le (residualLift (blockProjection K e) x).subtype (pCore 2 K)

/-- Its entire intrinsic core commutator is contained in the original layer. -/
theorem replacement_core_commutator_le (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) :
    (blockU (replacement K e x)).map (replacement K e x).subtype ≤
      (blockU K).map K.subtype := by
  simp only [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact commutator_mono (replacement_core_le K e x) (replacement_le K e x)

/-- Average in any elementary invariant layer containing the replacement's
core commutator, on the actual checked quotient. -/

theorem checked_centralizes_of_elementary_layer
    (L K T U : Subgroup G) [IsElementaryAbelian 2 U] (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hU : U ≤ Gv v) (hperfect : IsPPerfect 2 K)
    (hKU : K ≤ normalizer (U : Set G))
    (hcore : (blockU K).map K.subtype ≤ U) (hn : T ≤ normalizer (K : Set G))
    (S : Sylow 2 (Gv v)) (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = T)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ T)
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hLK : Lv L v ≤ K)
    (hfix : U ⊓ centralizer (Lv L v : Set G) =
      U ⊓ centralizer (K : Set G))
    (a : Gv v) (haD : (a : G) ∈ centralizer (Lv L v : Set G))
    (ha : checkedQuotientMap v a ∈ centralizer (checkedImage v T : Set (Gcheck v))) :
    K ≤ Gv (a : G) := by
  let : Finite (Gcheck v) := inferInstanceAs (Finite (Gv v ⧸ vLine v))
  let q := CenterPreimage.checkedKMap K v hK
  have hq := CenterPreimage.checkedKMap_surjective K v hK
  let Sc : Sylow 2 (Gcheck v) := S.mapSurjective (QuotientGroup.mk'_surjective (vLine v))
  have hSc : (Sc : Subgroup (Gcheck v)) = checkedImage v T := by
    rw [← hS, checkedImage]
    rw [show (((S : Subgroup (Gv v)).map (Gv v).subtype).subgroupOf (Gv v)) = S from
      comap_map_eq_self_of_injective (Gv v).subtype_injective _]
    rfl
  have hnC : (Sc : Subgroup (Gcheck v)) ≤ normalizer (checkedImage v K : Set (Gcheck v)) := by
    rw [hSc]
    exact SourceActors.image_normalizes (checkedQuotientMap v) hn
  have hnorm : checkedImage v K ≤ normalizer
      (checkedImage v U : Set (Gcheck v)) :=
    SourceActors.image_normalizes (checkedQuotientMap v) hKU
  have hPc : ((P.mapSurjective hq : Sylow 2 (checkedImage v K)) : Subgroup _).map
      (checkedImage v K).subtype ≤ Sc := by
    rw [Sylow.coe_mapSurjective, ← checked_map K v hK, hSc]
    exact map_mono (comap_mono hP)
  have hchar : centralizer (pCore 2 (Gcheck v) : Set (Gcheck v)) ≤ pCore 2 (Gcheck v) :=
    (CFSG.Quasithin.ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      (CFSG.Quasithin.ChapterA.lemma_A_1_8 2 hf (vLine v) (vLine_le_center v))
  let : IsElementaryAbelian 2 (U.subgroupOf (Gv v)) :=
    IsElementaryAbelian.subgroupOf hU
  let : IsElementaryAbelian 2 (checkedImage v U) := IsElementaryAbelian.map _
  apply Source.centralizes_of_checked_centralizes K v a hK hperfect hv
  apply mem_centralizer_of_sylow_fixed_core_comparison Sc (checkedImage v K) (checkedImage v (Lv L v))
    (checkedImage v U) hchar
    (hperfect.of_surjective q hq) hnC hnorm
    ((checked_core_commutator K v hK hv).ge.trans (map_mono (comap_mono hcore))) (P.mapSurjective hq) hPc
    (map_mono (comap_mono hLK))
    (SourceSmallModels.checked_centralizer_eq_of_ambient L K _ v hLK hv hfix)
    (checkedQuotientMap v a) (by
      change checkedQuotientMap v a ∈ centralizer ((Sc : Subgroup (Gcheck v)) : Set (Gcheck v))
      rwa [hSc])
  rintro _ ⟨x, hx, rfl⟩
  exact congrArg (checkedQuotientMap v) (Subtype.ext (haD x hx))


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
