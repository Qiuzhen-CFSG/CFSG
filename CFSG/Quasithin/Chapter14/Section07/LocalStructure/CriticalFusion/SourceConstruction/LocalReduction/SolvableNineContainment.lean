module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableCubicContainment
public import Theory.GroupTheory.PGroup.ElementaryNineCubicLifts

/-!
# Containment of the elementary-nine lift in the original solvable witness

The original point image is a Sylow-invariant cubic line of the normal
nine-group. A coprime complement and normalized residual lifts give two
cubic generators, each contained in the seed normalizer by the relative
cubic argument. Hence the entire normal lift lies there.

The application retains the original minimal witness, both quotient models,
the exact two-core kernels and the Heisenberg center marking. Containment
of the nine-lift is the intermediate step in 14.5.20; the subsequent
cyclic-nine enlargement and terminal solvable exclusion remain required.

Source: Aschbacher–Smith, 14.5.20, printed p.1019, and 14.7.27–29,
pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal elementary-nine two-perfect lift containing the actual point
residual is contained in the seed normalizer. -/
theorem local_solvable_nine_lift_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    Y.map J.subtype ≤ normalizer (L : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let eP := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsElementaryAbelian 3 (Y.map q) :=
    IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  have hP : Nat.card (Y.map q) = 9 := by
    rw [Nat.card_congr eP.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  let C := ((F.Li L 1).subgroupOf J).map q
  have hC : Nat.card C = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hSC : (S : Subgroup J).map q ≤ normalizer (C : Set (HStar J)) := by
    apply (map_mono ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    exact fun _ hx => T_normalizes_L₁ h structural hx
  obtain ⟨A,B,hAB,⟨hAp,hAT,_,_,hAc⟩,⟨hBp,hBT,_,hBc⟩⟩ :=
    exists_cubic_lifts_of_normal_elementary_nine q (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      Y hYp hP S S.isPGroup' C (map_mono hAY) hC hSC
  have hn := local_nine_lift_normalizes_point h structural J hJ Y hAY e
  have hcontain (A : Subgroup J) (hA : A ≤ Y) (hp : IsPPerfect 2 A)
      (hAT : (S : Subgroup J) ≤ normalizer (A : Set J))
      (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
      A.map J.subtype ≤ normalizer (L : Set G) := by
    have hmap : IsPPerfect 2 (A.map J.subtype) := hp.of_surjective
      (J.subtype.subgroupMap A) (J.subtype.subgroupMap_surjective A)
    have hnorm : (T : Subgroup G) ≤ normalizer (A.map J.subtype : Set G) := by
      have hh := (map_mono hAT).trans (le_normalizer_map J.subtype)
      rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)] at hh
    let eA := equivMapOfInjective A J.subtype J.subtype_injective
    have hcard : Nat.card ((A.map J.subtype) ⧸ pCore 2 (A.map J.subtype)) = 3 := by
      rw [←Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv]
      exact hc
    exact local_solvable_cubic_containment h hab structural previous faithful J hJ hs
      (A.map J.subtype) (map_subtype_le A) ((map_mono hA).trans hn) hmap hnorm hcard
  rw [←hAB,Subgroup.map_sup]
  exact sup_le (hcontain A (le_sup_left.trans_eq hAB) hAp hAT hAc)
    (hcontain B (le_sup_right.trans_eq hAB) hBp hBT hBc)

/-- On the original minimal solvable witness, the normal nine-lift is
contained in M; the Heisenberg branch retains its exact center marking. -/
theorem local_minimal_solvable_threeCore_nine_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      (∀ A : Subgroup G, A ≤ Y.map I.subtype → IsPPerfect 2 A →
        (T : Subgroup G) ≤ normalizer (A : Set G) →
        Nat.card (A ⧸ pCore 2 A) = 3 →
        A ≤ normalizer (L : Set G)) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I) ∧
          Y.map I.subtype ≤ normalizer (L : Set G)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hc,he⟩ :=
    local_minimal_solvable_threeCore_cubic_containment h hab structural previous faithful J hJ hs
  let := hYn
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hc,?_⟩
  rcases he with ⟨he,hr⟩ | he
  · exact Or.inl ⟨he,hr,local_solvable_nine_lift_containment h hab structural previous faithful
      I hI hIs Y hYp hAY he.some⟩
  · exact Or.inr he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
