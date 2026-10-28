module

public import Theory.GroupTheory.SylowFixedCoreCentralizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CenterPreimage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.SourceActors
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic

/-!
# The checked short-block endgame without a splitting premise

The actual checked map K → Ǩ has a central two-group kernel, so it maps
[O₂(K),K] onto [O₂(Ǩ),Ǩ]. A.1.8 gives characteristic two in C_G(v)/⟨v⟩.
The previous Sylow averaging theorem therefore applies to its literal
Sylow-central point and the checked fixed-space comparison. Two-perfection
then lifts centralization through the specified kernel ⟨v⟩.

This removes F, its commutativity and membership witnesses, and the supplied
B.2.14 splitting from the short-block branches of 13.6.22. The source family
must still establish its fixed-space comparison; the binary rank-two source
application does this using the already constructed parabolic and cubic.

Source: Aschbacher–Smith, 13.6.22, printed pp.932–933, using B.2.14 and A.1.8.
-/

public section
open Subgroup CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
open BinaryRankTwo
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The block layer is transported by the literal checked map. -/
theorem checked_map (K : Subgroup G) (v : G) (hK : K ≤ Gv v) (A : Subgroup K) :
    checkedImage v (A.map K.subtype) =
      (A.map (CenterPreimage.checkedKMap K v hK)).map (checkedImage v K).subtype := by
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk, he⟩, rfl⟩
    refine ⟨CenterPreimage.checkedKMap K v hK k, mem_map_of_mem _ hk, ?_⟩
    exact congrArg (checkedQuotientMap v) (Subtype.ext he)
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨inclusion hK k, mem_map_of_mem _ hk, rfl⟩

/-- The two-group checked kernel preserves the intrinsic core commutator. -/
theorem checked_core_commutator (K : Subgroup G) (v : G) (hK : K ≤ Gv v)
    (hv : v ^ 2 = 1) :
    checkedImage v ((blockU K).map K.subtype) =
      (blockU (checkedImage v K)).map (checkedImage v K).subtype := by
  let : Finite (Gcheck v) := inferInstanceAs (Finite (Gv v ⧸ vLine v))
  rw [checked_map K v hK]
  congr 1
  let q := CenterPreimage.checkedKMap K v hK
  have hq := CenterPreimage.checkedKMap_surjective K v hK
  have hc : (pCore 2 K).map q = pCore 2 (checkedImage v K) := by
    rw [← q.comap_pCore_of_ker_isPGroup hq (CenterPreimage.checkedKMap_pKernel K v hK hv),
      map_comap_eq_self_of_surjective hq]
  rw [blockU, map_commutator, hc, map_top_of_surjective _ hq]
  rfl

/-- The short-block endgame, with the B.2.14 supplement discharged by Sylow
averaging on the same checked quotient and earlier source point. -/
theorem checked_centralizes_short
    (L K T : Subgroup G) (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hshort : IsShort K) (hn : T ≤ normalizer (K : Set G))
    (S : Sylow 2 (Gv v)) (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = T)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ T)
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hLK : Lv L v ≤ K)
    (hfix : ((blockU K).map K.subtype) ⊓ centralizer (Lv L v : Set G) =
      ((blockU K).map K.subtype) ⊓ centralizer (K : Set G))
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
      (checkedImage v ((blockU K).map K.subtype) : Set (Gcheck v)) :=
    SourceActors.image_normalizes (checkedQuotientMap v) (Models.ambientU_normalizes K)
  have hPc : ((P.mapSurjective hq : Sylow 2 (checkedImage v K)) : Subgroup _).map
      (checkedImage v K).subtype ≤ Sc := by
    rw [Sylow.coe_mapSurjective, ← checked_map K v hK, hSc]
    exact map_mono (comap_mono hP)
  have hchar : centralizer (pCore 2 (Gcheck v) : Set (Gcheck v)) ≤ pCore 2 (Gcheck v) :=
    (CFSG.Quasithin.ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      (CFSG.Quasithin.ChapterA.lemma_A_1_8 2 hf (vLine v) (vLine_le_center v))
  let : IsElementaryAbelian 2 (blockU K) := hshort.elementary
  let : IsElementaryAbelian 2 ((blockU K).map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 (checkedImage v ((blockU K).map K.subtype)) := by
    rw [checked_map K v hK]
    exact IsElementaryAbelian.map _
  apply Source.centralizes_of_checked_centralizes K v a hK hshort.twoPerfect hv
  apply mem_centralizer_of_sylow_fixed_core_comparison Sc (checkedImage v K) (checkedImage v (Lv L v))
    (checkedImage v ((blockU K).map K.subtype)) hchar
    (hshort.twoPerfect.of_surjective q hq) hnC hnorm
    (checked_core_commutator K v hK hv).ge (P.mapSurjective hq) hPc
    (map_mono (comap_mono hLK))
    (SourceSmallModels.checked_centralizer_eq_of_ambient L K _ v hLK hv hfix)
    (checkedQuotientMap v a) (by
      change checkedQuotientMap v a ∈ centralizer ((Sc : Subgroup (Gcheck v)) : Set (Gcheck v))
      rwa [hSc])
  rintro _ ⟨x, hx, rfl⟩
  exact congrArg (checkedQuotientMap v) (Subtype.ext (haD x hx))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
