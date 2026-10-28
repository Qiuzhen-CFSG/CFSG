module
public import Theory.GroupTheory.SylowFixedCenterCentralizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.CheckedShortAction

/-!
# The checked endgame from the source center commutator

The literal image of Z₀ is Z(O₂(Ǩ)). Thus the source identity [Z₀,K]=U
maps to [Z(O₂(Ǩ)),Ǩ]=Ŭ. A.1.8 gives characteristic two in
C_G(v)/⟨v⟩, and the center-commutator averaging theorem makes the same
Sylow-central source point fixed by Ǩ when its U-fixed spaces agree.
Two-perfection lifts this fixation through the specified central two-group
kernel ⟨v⟩.

Unlike the short-block theorem, this application allows a nonabelian
core commutator: only the source center commutator U must be elementary.
Its model realization, the literal center-preimage identity and the
ambient fixed-space comparison remain with the source-family producers.

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
/-- The literal checked image of the source center preimage. -/
theorem checked_sourceZ0 (K : Subgroup G) (v : G) (hK : K ≤ Gv v) :
    checkedImage v (CenterPreimage.sourceZ0 K v hK) =
      ((center (pCore 2 (checkedImage v K))).map (pCore 2 (checkedImage v K)).subtype).map
        (checkedImage v K).subtype := by
  rw [CenterPreimage.sourceZ0, checked_map K v hK,
    map_comap_eq_self_of_surjective (CenterPreimage.checkedKMap_surjective K v hK)]

omit [Finite G] in
/-- The source identity gives exactly the center commutator of Ǩ. -/
theorem checked_center_commutator (K U : Subgroup G) (v : G) (hK : K ≤ Gv v)
    (hc : ⁅CenterPreimage.sourceZ0 K v hK, K⁆ = U) :
    ⁅((center (pCore 2 (checkedImage v K))).map (pCore 2 (checkedImage v K)).subtype).map
        (checkedImage v K).subtype, checkedImage v K⁆ = checkedImage v U := by
  have hz : CenterPreimage.sourceZ0 K v hK ≤ Gv v := (map_subtype_le _).trans hK
  rw [← checked_sourceZ0 K v hK, ← checkedImage_commutator v _ K hz hK, hc]

/-- The center-preimage endgame for the original nonshort source cases. -/
theorem checked_centralizes_of_center_preimage_commutator
    (L K T U : Subgroup G) [IsElementaryAbelian 2 U]
    (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hperfect : IsPPerfect 2 K)
    (hcenter : ⁅CenterPreimage.sourceZ0 K v hK, K⁆ = U)
    (hn : T ≤ normalizer (K : Set G))
    (S : Sylow 2 (Gv v)) (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = T)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ T)
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hLK : Lv L v ≤ K)
    (hfix : U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G))
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
  have hKU : K ≤ normalizer (U : Set G) := by
    rw [← hcenter]
    exact normalizer_commutator_ge_right _ _
  have hU : U ≤ Gv v := by
    rw [← hcenter]
    exact (Subgroup.commutator_le_sup _ _).trans (sup_le ((map_subtype_le _).trans hK) hK)
  have hnorm : checkedImage v K ≤ normalizer (checkedImage v U : Set (Gcheck v)) :=
    SourceActors.image_normalizes (checkedQuotientMap v) hKU
  have hPc : ((P.mapSurjective hq : Sylow 2 (checkedImage v K)) : Subgroup _).map
      (checkedImage v K).subtype ≤ Sc := by
    rw [Sylow.coe_mapSurjective, ← checked_map K v hK, hSc]
    exact map_mono (comap_mono hP)
  have hchar : centralizer (pCore 2 (Gcheck v) : Set (Gcheck v)) ≤ pCore 2 (Gcheck v) :=
    (CFSG.Quasithin.ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      (CFSG.Quasithin.ChapterA.lemma_A_1_8 2 hf (vLine v) (vLine_le_center v))
  let : IsElementaryAbelian 2 (U.subgroupOf (Gv v)) := IsElementaryAbelian.subgroupOf hU
  let : IsElementaryAbelian 2 (checkedImage v U) := IsElementaryAbelian.map _
  apply Source.centralizes_of_checked_centralizes K v a hK hperfect hv
  apply mem_centralizer_of_sylow_fixed_center_comparison Sc (checkedImage v K)
    (checkedImage v (Lv L v)) (checkedImage v U) hchar (hperfect.of_surjective q hq)
    hnC hnorm (checked_center_commutator K U v hK hcenter).le (P.mapSurjective hq) hPc
    (map_mono (comap_mono hLK))
    (checked_centralizer_eq_of_ambient L K U v hLK hv hfix)
    (checkedQuotientMap v a) (by
      change checkedQuotientMap v a ∈ centralizer ((Sc : Subgroup (Gcheck v)) : Set (Gcheck v))
      rwa [hSc])
  rintro _ ⟨x, hx, rfl⟩
  exact congrArg (checkedQuotientMap v) (Subtype.ext (haD x hx))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
