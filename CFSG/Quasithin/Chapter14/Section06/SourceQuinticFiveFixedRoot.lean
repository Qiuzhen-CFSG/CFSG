module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualCenter

/-!
# The actual root alternative in the large quintic core

The five-fixed subgroup has order four and intersects the order-512
residual in the original central line. If cyclic, its generator is an
actual root outside the residual whose square generates that line. If
noncyclic, it supplies an actual fixed involution outside the residual.
Both alternatives retain the full order-1024 core and order-64 kernel.
No cyclicity, residual class, or model recognition is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original large branch supplies either the marked cyclic-four root
or a concrete five-fixed involution for the remaining fusion argument. -/
theorem source_quintic_large_five_fixed_root_alternative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    let B := Q ⊓ centralizer (A : Set G)
    let R := ⁅Q,A⁆
    Nat.card C = 64 ∧ Nat.card Q = 1024 ∧
      ((∃ t : G, t ∈ B ∧ t ∉ R ∧ orderOf t = 4 ∧ zpowers t = B ∧
        zpowers (t ^ 2) = centralInvolutions T ∧ R ⊔ zpowers t = Q ∧
        t ∈ centralizer (U : Set G)) ∨
      (∃ y : G, y ∈ B ∧ y ∉ R ∧ orderOf y = 2 ∧
        y ∈ centralizer (U : Set G))) := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let B := Q ⊓ centralizer (A : Set G)
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  obtain ⟨hCcard, hQcard, hBcard, _, _, _, _, _⟩ :=
    source_quintic_large_five_residual hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA
  obtain ⟨hRB, hcap, _, _, _, _⟩ := source_quintic_large_five_residual_center
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hBC : B ≤ C := (source_quintic_five_centralizers
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA).2.le.trans inf_le_left
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hnot : ¬ B ≤ R := by
    intro hBR
    have hBZ : B ≤ Z := by
      intro b hb
      exact hcap.le ⟨hBR hb, hb⟩
    have hh := card_le_of_le hBZ
    change Nat.card B ≤ Nat.card Z at hh
    rw [hBcard, hZcard] at hh
    omega
  refine ⟨hCcard, hQcard, ?_⟩
  by_cases hcyclic : IsCyclic B
  · let : IsCyclic B := hcyclic
    obtain ⟨t, ht⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyclic
    have ht4B : orderOf t = 4 := ht.trans hBcard
    have ht4 : orderOf (t : G) = 4 := by simpa only [orderOf_coe] using ht4B
    have hgen : zpowers (t : G) = B :=
      eq_of_le_of_card_ge (zpowers_le.mpr t.property) (by rw [Nat.card_zpowers, ht4, hBcard])
    have htR : (t : G) ∉ R := fun hh => hnot (hgen ▸ zpowers_le.mpr hh)
    have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
    let : Fact (IsPGroup 2 C) := ⟨(isPGroup_pCoreIn 2 H).to_le hCQ⟩
    have ht2Z : (t : G) ^ 2 ∈ Z :=
      source_quintic_full_kernel_frattini_le_point hG T hempty hM hu hmany hcard e H hH hi
        (mem_map_of_mem C.subtype
          (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨t, hBC t.property⟩ : C)))
    have hsq : zpowers ((t : G) ^ 2) = Z := by
      apply eq_of_le_of_card_ge (zpowers_le.mpr ht2Z)
      rw [Nat.card_zpowers, orderOf_pow, ht4, hZcard]
      decide
    exact Or.inl ⟨t, t.property, htR, ht4, hgen, hsq, hgen.symm ▸ hRB,
      (hBC t.property).2⟩
  · obtain ⟨y, hyB, hyR⟩ := SetLike.not_le_iff_exists.mp hnot
    let yB : B := ⟨y, hyB⟩
    have hexp : Monoid.exponent B = 2 :=
      (not_isCyclic_iff_exponent_eq_prime Nat.prime_two hBcard).mp hcyclic
    have hy2 : y ^ 2 = 1 := congrArg B.subtype (show yB ^ 2 = 1 by
      rw [← hexp]; exact Monoid.pow_exponent_eq_one yB)
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Or.inr ⟨y, hyB, hyR, orderOf_eq_prime hy2
      (fun hh => hyR (hh ▸ R.one_mem)), (hBC hyB).2⟩

end CFSG.Quasithin.Chapter14.Section06
