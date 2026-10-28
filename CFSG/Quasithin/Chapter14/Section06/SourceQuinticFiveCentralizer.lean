module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanOrder
public import Theory.GroupTheory.FiveThirtyTwoTwoCentralizer

/-!
# Actual five-centralizers with the full quintic kernel retained

An actual order-five subgroup of H fixes exactly ZT in UH. Its centralizer
in the full two-core lies in the original kernel C=H intersect C_G(UH).
This does not identify that centralizer with ZT: the full C is retained,
including in the FullRee case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Every actual five-subgroup fixes the central line in UH, and all its
fixed points in the two-core already lie in the whole radius-two kernel. -/
theorem source_quintic_five_centralizers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    U ⊓ centralizer (A : Set G) = centralInvolutions T ∧
      H.pCoreIn 2 ⊓ centralizer (A : Set G) = C ⊓ centralizer (A : Set G) := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let D := Q ⊓ centralizer (A : Set G)
  have hUcard : Nat.card U = 32 := (source_quintic_span_card_and_core_radical
    hG T hempty hM hu hmany hcard e H hH hi).1
  let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core
    hG T hM H hH hi
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)).2.2.2.2.2.2
  let : MulDistribMulAction H U :=
    conjMulDistribMulActionOfLeNormalizer H U (le_normalizer_conjugateSpanBy _ _)
  let f : H →* MulAut U := MulDistribMulAction.toMulAut H U
  have hk : f.ker = C.subgroupOf H := by
    ext h
    constructor
    · intro hh
      refine ⟨h.property,?_⟩
      intro u hu'
      have hx := congrArg U.subtype (DFunLike.congr_fun (show f h = 1 from hh) ⟨u,hu'⟩)
      change (h:G)*u*(h:G)⁻¹=u at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    · intro hh
      change f h = 1
      ext u
      change (h:G)*(u:G)*(h:G)⁻¹=(u:G)
      have he : (h:G)*(u:G)=(u:G)*(h:G) :=
        (mem_centralizer_iff.mp hh.2 u u.property).symm
      rw [he,mul_inv_cancel_right]
  have hkQ : f.ker ≤ pCore 2 H := by
    rw [hk]
    intro h hh
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp (hCQ hh)
  have hDH : D ≤ H := inf_le_left.trans (pCoreIn_le 2 H)
  have hDQ : D.subgroupOf H ≤ pCore 2 H := by
    intro d hd
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp hd.1
  have hDC : D ≤ C := by
    have hh := two_subgroup_le_kernel_of_centralizes_five_on_thirtyTwo f
      (pCore_isPGroup.to_le hkQ) hUcard (A.subgroupOf H) (D.subgroupOf H)
      ((Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA)
      (pCore_isPGroup.to_le hDQ) (by
        intro d hd a ha
        exact Subtype.ext (hd.2 a ha))
    rw [hk] at hh
    intro d hd
    exact hh (show (⟨d,hDH hd⟩ : H) ∈ D.subgroupOf H from hd)
  have hD : D = C ⊓ centralizer (A : Set G) :=
    le_antisymm (le_inf hDC inf_le_right) (inf_le_inf_right _ hCQ)
  refine ⟨?_,hD⟩
  let : MulDistribMulAction A U :=
    conjMulDistribMulActionOfLeNormalizer A U
      (hAH.trans (le_normalizer_conjugateSpanBy _ _))
  let F := FixedPoints.subgroup A U
  have hFne : F ≠ ⊤ := by
    intro ht
    have hAQ : A ≤ Q := by
      intro a ha
      apply hCQ
      refine ⟨hAH ha,?_⟩
      intro u hu'
      have hh := congrArg U.subtype ((show (⟨u,hu'⟩ : U) ∈ F from ht ▸ mem_top _) ⟨a,ha⟩)
      change a*u*a⁻¹=u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hp := (isPGroup_pCoreIn 2 H).to_le hAQ
    have hdiv : 2 ∣ Nat.card A := by
      rcases hp.card_eq_or_dvd with he | hd
      · omega
      · exact hd
    norm_num [hA] at hdiv
  have hFcard : Nat.card F = 2 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hmod := (IsPGroup.of_card (p := 5) (G := A) (n := 1)
      (by simpa using hA)).card_modEq_card_fixedPoints U
    change Nat.card U % 5 = Nat.card F % 5 at hmod
    rw [hUcard] at hmod
    have hdiv : Nat.card F ∣ 32 := hUcard ▸ F.card_subgroup_dvd_card
    have hmem := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show (32 : ℕ).divisors = {1,2,4,8,16,32} by decide] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    have hn : Nat.card F ≠ 32 := fun hh =>
      hFne (F.eq_top_of_card_eq (hh.trans hUcard.symm))
    omega
  have hZF : Z.subgroupOf U ≤ F := by
    intro z hz a
    apply Subtype.ext
    change (a:G)*(z:G)*(a:G)⁻¹=(z:G)
    rw [←mem_centralizer_iff.mp (hHZ (hAH a.property)) z hz,mul_inv_cancel_right]
  have hZcard : Nat.card (Z.subgroupOf U) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZeq : Z.subgroupOf U = F := eq_of_le_of_card_ge hZF (by rw [hZcard,hFcard])
  apply le_antisymm
  · intro u hu'
    have hc : (⟨u,hu'.1⟩ : U) ∈ F := by
      intro a
      apply Subtype.ext
      change (a:G)*u*(a:G)⁻¹=u
      rw [mem_centralizer_iff.mp hu'.2 a a.property,mul_inv_cancel_right]
    exact hZeq.ge hc
  · exact le_inf hZU (le_centralizer_iff.mp (hAH.trans hHZ))

end CFSG.Quasithin.Chapter14.Section06
