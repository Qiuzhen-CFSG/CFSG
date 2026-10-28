module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Source
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.Centerless
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# The original local actor in the ordinary A₇ replacement

The residual Lᵥ has cubic quotient by its two-core. Its faithful plus image
is nontrivial by the earlier source commutator, hence has a two-group kernel
and the same cubic core quotient. This proves the prime support and order of
its Sylow three-subgroups used by the seven-letter normalizer calculation.
Relative normality and the Baumann-normalizer bound are obtained on the
literal local groups of the original configuration.

Source: Aschbacher–Smith, 13.6.4–5, 13.6.11 and the ordinary A₇ paragraph
of 13.6.22, printed pp.927–928 and 932.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open ComponentSelection A5Module SourceContainment
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}

/-- The actual residual plus image retains the source cubic quotient. -/
theorem residual_plus_quotient_card
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hchar : generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    Nat.card (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz (Lv L (markedV d.flag.module)) ⧸
      pCore 2 (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz (Lv L (markedV d.flag.module)))) = 3 := by
  let s := d.flag.module
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV s)) (Gv (markedV s)) :=
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv (markedV s))) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Uv (markedZ s) (markedV s)) :=
    IsElementaryAbelian.of_le (Uv_le_coreOmega (T : Subgroup G) (markedZ s)
      (markedV s) hSylow (markedZ_mem_Tv_omega d) hchar)
  let D := plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz (Lv L (markedV s))
  have hD : D ≠ ⊥ := StarAction.plusImage_Lv_ne_bot s K (T : Subgroup G)
    c.reductions.centralizerSylow c.reductions.sylow_image hL hz hK hn
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD
  have hLA : Lv L (markedV s) ≤ plusActor K L (T : Subgroup G) (markedV s) :=
    le_sup_right.trans le_sup_left
  let f : Lv L (markedV s) →* D :=
    ((plusMk K L (T : Subgroup G) (markedZ s) (markedV s) hL hz).subgroupMap
      ((Lv L (markedV s)).subgroupOf (plusActor K L (T : Subgroup G) (markedV s)))).comp
      (subgroupOfEquivOfLe hLA).symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((plusMk K L (T : Subgroup G) (markedZ s) (markedV s) hL hz).subgroupMap_surjective _).comp
      (subgroupOfEquivOfLe hLA).symm.surjective
  have hfn : f.range ≠ ⊥ := by
    rw [MonoidHom.range_eq_top.mpr hf]
    exact top_ne_bot
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le
    (LinearThree.residual_image_kernel_le_twoCore L (markedV s) c.residual_card f hfn)
  exact (Nat.card_congr (f.quotientPCoreEquivOfSurjective hf hk).toEquiv).symm.trans c.residual_card

private theorem prime_support_of_cubic_quotient {H : Type*} [Group H] [Finite H]
    (hc : Nat.card (H ⧸ pCore 2 H) = 3) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  intro p hp hd
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 H), hc, hn] at hd
  rcases hp.dvd_mul.mp hd with h3 | h2
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))

private theorem sylow_three_card_of_cubic_quotient {H : Type*} [Group H] [Finite H]
    (hc : Nat.card (H ⧸ pCore 2 H) = 3) (P : Sylow 3 H) : Nat.card P = 3 := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  rw [P.card_eq_multiplicity, card_eq_card_quotient_mul_card_subgroup (pCore 2 H), hc, hn]
  simp [Nat.factorization_mul (by decide : 3 ≠ 0) (pow_ne_zero n (by decide : 2 ≠ 0)),
    Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3 ∣ 2)]

/-- The source supplies every prime-support and Sylow-three input in the
ordinary A₇ replacement, on its actual plus image. -/
theorem residual_plus_local_orders
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hchar : generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    (∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz (Lv L (markedV d.flag.module))) →
        p = 2 ∨ p = 3) ∧
    (∀ P : Sylow 3 (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz (Lv L (markedV d.flag.module))), Nat.card P = 3) := by
  have hc := residual_plus_quotient_card d c hK hn hchar hL hz
  exact ⟨prime_support_of_cubic_quotient hc, sylow_three_card_of_cubic_quotient hc⟩

/-- Relative normality and the Baumann-normalizer placement use the same
local residual and the same Tv as the original configuration. -/
theorem residual_local_normality_and_baumann
    (d : FlagSource T L V V₁ V₂)
    (c : LocalConfiguration (normalizer (L : Set G)) d.flag) :
    Lv L (markedV d.flag.module) ≤ Mv (normalizer (L : Set G)) (markedV d.flag.module) ∧
    ((Lv L (markedV d.flag.module)).subgroupOf
      (Mv (normalizer (L : Set G)) (markedV d.flag.module))).Normal ∧
    Gv (markedV d.flag.module) ⊓ normalizer
      (ChapterB.baumann (Tv (T : Subgroup G) (markedV d.flag.module)) : Set G) ≤
        Mv (normalizer (L : Set G)) (markedV d.flag.module) := by
  refine ⟨?_, normal_subgroupOf_of_le_normalizer
    (AlternatingBranches.CoveredSix.Mv_normalizes_Lv le_rfl), ?_⟩
  · exact (map_subtype_le _).trans (inf_le_inf L.le_normalizer le_rfl)
  · rw [← c.reductions.baumann_eq]
    exact c.reductions.normalizer_baumann

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
