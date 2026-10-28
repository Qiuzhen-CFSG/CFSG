module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Normalizers
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.Commutator.ThompsonAB
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The normalizer and Thompson steps of 13.5.20

The actual map H → H/O₂(H) carries the two-core of N_H(Y) into the
embedded two-core of N_{H*}(Y*). For any normal three-subgroup P* of H*,
its Y*-centralizer is normal in that normalizer and lies in its three-core.
The two cores commute, so 13.5.19 makes C_{P*}(Y*) centralize V*.

If O₂(Y*) centralized P*, a Sylow three-subgroup of Y* would have the
same fixed subgroup as Y*. Thompson's A×B lemma then makes V* centralize
P*, a contradiction. Both source choices of Y have explicit applications
of the published 13.5.19 deductions below.

The cubic quotient and commutation with V* are earlier local inputs here.
This is a proof of the normalizer/Thompson step, not all of 13.5.20.
Source: Aschbacher–Smith, combined manuscript, printed p.923 (PDF p.940).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Source
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
variable {G : Type*} [Group G] [Finite G]

theorem starImage_core_le (H J : Subgroup G) (hJH : J ≤ H) :
    starImage H (J.pCoreIn 2) ≤ (starImage H J).pCoreIn 2 := by
  have he : (J.subgroupOf H).pCoreIn 2 = (J.pCoreIn 2).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hJH,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 J).trans hJH)]
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  change ((J.pCoreIn 2).subgroupOf H).map q ≤ _
  rw [← he, map_pCoreIn_of_ker_isPGroup q hk]
  exact le_rfl

private theorem core_normalizer_centralizes_fixed
    {X : Type*} [Group X] (P Y A : Subgroup X) [P.Normal]
    (hP : IsPGroup 3 P) (hA : A ≤ (normalizer (Y : Set X)).pCoreIn 2) :
    P ⊓ centralizer (Y : Set X) ≤ centralizer (A : Set X) := by
  let N := normalizer (Y : Set X)
  let C := P ⊓ centralizer (Y : Set X)
  have hCN : C ≤ N := inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hNC : N ≤ normalizer (C : Set X) :=
    (le_inf le_normalizer_of_normal (normalizer_le_normalizer_centralizer _)).trans
      inf_normalizer_le_normalizer_inf
  have hCcore : C ≤ N.pCoreIn 3 :=
    le_pCoreIn_of_normalizes (hP.to_le inf_le_left) hCN hNC
  intro c hc a ha
  obtain ⟨cN, hcN, rfl⟩ := hCcore hc
  obtain ⟨aN, haN, rfl⟩ := hA ha
  exact congrArg Subtype.val (pCore_commute_of_ne 2 3 (by decide) aN haN cN hcN)

/-- The fixed-subgroup premise in the Thompson argument follows from 13.5.19. -/
theorem fixed_centralizer_of_normalizer
    (H Y V : Subgroup G)
    (himage : starImage H (H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage H Y : Set (Hstar H)))
    (hcore : V ≤ (H ⊓ normalizer (Y : Set G)).pCoreIn 2)
    (P : Subgroup (Hstar H)) [P.Normal] (hP : IsPGroup 3 P) :
    P ⊓ centralizer (starImage H Y : Set (Hstar H)) ≤
      centralizer (starImage H V : Set (Hstar H)) := by
  apply core_normalizer_centralizes_fixed P (starImage H Y) (starImage H V) hP
  rw [← himage]
  exact (map_mono (comap_mono hcore)).trans
    (starImage_core_le H (H ⊓ normalizer (Y : Set G)) inf_le_left)

private theorem thompson_of_twoCore_centralizes
    {X : Type*} [Group X] [Finite X]
    (P Y A : Subgroup X) (hP : IsPGroup 3 P)
    (hquot : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hYA : Y ≤ centralizer (A : Set X))
    (hYP : Y ≤ normalizer (P : Set X))
    (hAP : A ≤ normalizer (P : Set X))
    (hA : IsPPerfect 3 A)
    (hfix : P ⊓ centralizer (Y : Set X) ≤ centralizer (A : Set X))
    (hcore : Y.pCoreIn 2 ≤ centralizer (P : Set X)) : ⁅P, A⁆ = ⊥ := by
  let S : Sylow 3 Y := default
  let B := (S : Subgroup Y).map Y.subtype
  have hBY : B ≤ Y := map_subtype_le _
  have hgen : B ⊔ Y.pCoreIn 2 = Y := by
    have hh := congrArg (Subgroup.map Y.subtype)
      (S.sup_eq_top_of_quotient_isPGroup (pCore 2 Y) hquot)
    simpa only [B, pCoreIn, Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] using hh
  apply thompson_a_times_b_centralizer A B P (S.isPGroup'.map Y.subtype) hP
    ((pResidual_eq_top_iff 3 A).mpr hA) (hBY.trans hYP) hAP
    (commutator_eq_bot_iff_le_centralizer.mpr (hBY.trans hYA))
  apply le_trans _ hfix
  apply le_inf inf_le_left
  rw [← hgen]
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    (hcore.trans (Subgroup.centralizer_le inf_le_left))

private theorem twoGroup_threePerfect {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup 2 A) : IsPPerfect 3 A := by
  apply (pResidual_eq_top_iff 3 A).mp
  apply top_unique
  intro a _
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  apply mem_pResidual_of_orderOf_coprime
  apply Nat.Coprime.of_dvd_right (orderOf_dvd_natCard a)
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

/-- The second paragraph of 13.5.20: the two-core of Y* must move P*. -/
theorem twoCore_moves_of_normalizer
    (H Y V : Subgroup G)
    (himage : starImage H (H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage H Y : Set (Hstar H)))
    (hcore : V ≤ (H ⊓ normalizer (Y : Set G)).pCoreIn 2)
    (hV : IsPGroup 2 V)
    (hquot : IsPGroup 3 (starImage H Y ⧸ pCore 2 (starImage H Y)))
    (hYV : starImage H Y ≤ centralizer (starImage H V : Set (Hstar H)))
    (P : Subgroup (Hstar H)) [P.Normal] (hP : IsPGroup 3 P)
    (hmove : ⁅P, starImage H V⁆ ≠ ⊥) :
    ¬ (starImage H Y).pCoreIn 2 ≤ centralizer (P : Set (Hstar H)) := by
  intro hcent
  apply hmove
  exact thompson_of_twoCore_centralizes P (starImage H Y) (starImage H V) hP
    hquot hYV le_normalizer_of_normal le_normalizer_of_normal
    (twoGroup_threePerfect (hV.comap_subtype.map (QuotientGroup.mk' (pCore 2 H))))
    (fixed_centralizer_of_normalizer H Y V himage hcore P hP) hcent

/-- Triple-cover application, with Y the actual residual L₀. -/
theorem covered_twoCore_moves
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) (M : Subgroup G)
    (hYH : Section08.ComponentSieve.FieldComponents.SmallCovers.coverResidualIn D.L ≤ D.H)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hbound : normalizer
      (Section08.ComponentSieve.FieldComponents.SmallCovers.coverResidualIn D.L : Set G) ≤ M)
    (hquot : IsPGroup 3
      (starImage D.H (Section08.ComponentSieve.FieldComponents.SmallCovers.coverResidualIn D.L) ⧸
        pCore 2 (starImage D.H (Section08.ComponentSieve.FieldComponents.SmallCovers.coverResidualIn D.L))))
    (hYV : starImage D.H (Section08.ComponentSieve.FieldComponents.SmallCovers.coverResidualIn D.L) ≤
      centralizer (starImage D.H D.V : Set (Hstar D.H)))
    (P : Subgroup (Hstar D.H)) [P.Normal] (hP : IsPGroup 3 P)
    (hmove : ⁅P, starImage D.H D.V⁆ ≠ ⊥) :
    ¬ (starImage D.H (Section08.ComponentSieve.FieldComponents.SmallCovers.coverResidualIn D.L)).pCoreIn 2 ≤
      centralizer (P : Set (Hstar D.H)) := by
  obtain ⟨hi, hc⟩ := covered_normalizer D h M hYH hVM hbound
  exact twoCore_moves_of_normalizer D.H _ D.V hi hc h.elementary.isPGroup hquot hYV P hP hmove

/-- Ordinary application, with Y the actual point residual L₁. The universal
nonnormality input is supplied by 13.5.18 from the counterexample hypothesis. -/
theorem ordinary_twoCore_moves
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) (M : Subgroup G)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hcentral : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (hF : ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis)
    (hnormal : ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → ¬ (D.L₁.subgroupOf J).Normal)
    (hquot : IsPGroup 3 (starImage D.H D.L₁ ⧸ pCore 2 (starImage D.H D.L₁)))
    (hYV : starImage D.H D.L₁ ≤ centralizer (starImage D.H D.V : Set (Hstar D.H)))
    (P : Subgroup (Hstar D.H)) [P.Normal] (hP : IsPGroup 3 P)
    (hmove : ⁅P, starImage D.H D.V⁆ ≠ ⊥) :
    ¬ (starImage D.H D.L₁).pCoreIn 2 ≤ centralizer (P : Set (Hstar D.H)) := by
  exact twoCore_moves_of_normalizer D.H D.L₁ D.V (local_normalizer_image D h)
    (local_normalizer_core D h M hVM hbound hcentral hF hnormal)
    h.elementary.isPGroup hquot hYV P hP hmove

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting

end
