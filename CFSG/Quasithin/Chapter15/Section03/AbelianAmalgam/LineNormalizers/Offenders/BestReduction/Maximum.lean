module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.PairedSection

/-!
# Best offenders on the whole internal module

For every subgroup of the faithful image of a maximum elementary subgroup A,
take its preimage X in A and compare A with `X C_U(X)`. The action kernel is
the same in A and X, and `X ∩ U = A ∩ U = C_U(A)`. The resulting cardinal
inequality is the best-offender comparison for every image subgroup, not just
the comparison with the trivial subgroup. Taking joins gives the corresponding
containment for the actual maximum-elementary Thompson image.

This result concerns U itself. Passage through U/E to the first marked summand
still needs the special core/transvection geometry of 15.3.67.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.2–3,
printed p.68, B.2.4 (pp.75–76), and proof of 15.3.67 (pp.1153–1154).
-/

public section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
variable {G H : Type*} [Group G] [Group H] [Finite G]

private theorem card_pow_rank (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ rank A := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  simp only [rank, hn, Nat.log_pow Nat.one_lt_two]

/-- The maximum-family comparison needed for every subgroup, using the actual
elementary replacement `X C_U(X)`. -/
theorem maximum_fixed_weight_comparison (S U A X : Subgroup G)
    [IsElementaryAbelian 2 U] (hUS : U ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hXA : X ≤ A) (hAX : A ⊓ U ≤ X) :
    rank X + rank (U ⊓ centralizer (X : Set G)) ≤
      rank A + rank (U ⊓ centralizer (A : Set G)) := by
  let F := U ⊓ centralizer (X : Set G)
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le hXA
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (X ⊓ F : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have he : IsElementaryAbelian 2 (X ⊔ F : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  let := he
  have hi : X ⊓ F = A ⊓ U := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans hXA) (inf_le_right.trans inf_le_left)
    · exact le_inf hAX (le_inf inf_le_right (hAX.trans X.le_centralizer))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes X F
    ((show F ≤ centralizer (X : Set G) from inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [card_pow_rank X, card_pow_rank F, card_pow_rank (X ⊓ F),
    card_pow_rank (X ⊔ F), ← pow_add, ← pow_add] at hc
  have hr := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  have hm : rank (X ⊔ F) ≤ rank A := Nat.log_mono_right
    (hA.2.2 _ (sup_le (hXA.trans hA.1) (inf_le_left.trans hUS)) he)
  rw [hi, ← max_fixed_eq_inf S U A hUS hA] at hr
  change rank X + rank F ≤ _
  omega

/-- Every nontrivial faithful image of a maximum elementary subgroup is best
on the whole internal module. -/
theorem maximum_image_isBestOffender (S U A : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U] (hUS : U ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (hne : A.map f ≠ ⊥) :
    IsBestOffender (Representation.NormalElementaryQuotient.representation U f hf hker)
      (A.map f) := by
  let ρ := Representation.NormalElementaryQuotient.representation U f hf hker
  let : IsElementaryAbelian 2 A := hA.2.1
  refine ⟨⟨hne, IsElementaryAbelian.map f⟩, ?_⟩
  intro B hBA
  let X := A ⊓ B.comap f
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le inf_le_left
  have hX : X.map f = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := hBA hb
      exact ⟨a, ⟨ha, hb⟩, rfl⟩
  have hk : X ⊓ f.ker = A ⊓ f.ker := by
    apply le_antisymm
    · exact inf_le_inf inf_le_left le_rfl
    · intro a ha
      exact ⟨⟨ha.1, by change f a ∈ B; rw [ha.2]; exact B.one_mem⟩, ha.2⟩
  have hAX : A ⊓ U ≤ X := by
    intro a ha
    refine ⟨ha.1, ?_⟩
    have haK : a ∈ f.ker := hker.symm ▸ U.le_centralizer ha.2
    change f a ∈ B
    rw [haK]
    exact B.one_mem
  have hw := maximum_fixed_weight_comparison S U A X hUS hA inf_le_left hAX
  have hAr := rank_kernel_add_image A f
  have hXr := rank_kernel_add_image X f
  rw [hk, hX] at hXr
  have hF (Y : Subgroup G) : rank (U ⊓ centralizer (Y : Set G)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (Y.map f)) := by
    rw [rank, ← Nat.card_congr
      (Representation.NormalElementaryQuotient.fixedSpaceEquiv U f hf hker Y)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Nat.log_pow Nat.one_lt_two]
  rw [hF X, hF A, hX] at hw
  change rank B + Module.finrank (ZMod 2) (fixedSpace ρ B) ≤
    rank (A.map f) + Module.finrank (ZMod 2) (fixedSpace ρ (A.map f))
  omega

/-- The actual Thompson image is contained in the best-offender-generated
subgroup on U. This does not replace the required comparison on U/E. -/
theorem thompson_image_le_internal_offenderSubgroup (S U : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U] (hUS : U ≤ S)
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) :
    (elementaryAbelianMaxJ S).map f ≤
      offenderSubgroup (Representation.NormalElementaryQuotient.representation U f hf hker) := by
  rw [map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hne : A.map f = ⊥
  · rw [hne]
    exact bot_le
  · have hb := maximum_image_isBestOffender S U A hUS hA f hf hker hne
    exact le_iSup_of_le (A.map f) (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)

omit [Finite G] in
/-- Bestness of the maximum-family images gives the exact intrinsic generation
statement required by B.5. It does not assert equality with the offender
subgroup of a larger actor. -/
theorem thompson_image_generated_of_maximum_images_best
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Subgroup G) (f : G →* H) (σ : Representation (ZMod 2) H W)
    (hbest : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      A.map f ≠ ⊥ → IsBestOffender σ (A.map f)) :
    offenderSubgroup (σ.comp ((elementaryAbelianMaxJ S).map f).subtype) = ⊤ := by
  let I := (elementaryAbelianMaxJ S).map f
  have hI : I ≤ (offenderSubgroup (σ.comp I.subtype)).map I.subtype := by
    change (elementaryAbelianMaxJ S).map f ≤ _
    rw [map_le_iff_le_comap]
    apply sSup_le
    intro A hA
    apply map_le_iff_le_comap.mp
    by_cases hne : A.map f = ⊥
    · rw [hne]
      exact bot_le
    · have hAI : A.map f ≤ I := map_mono (le_sSup hA)
      have hb := (hbest A hA hne).subgroupOf σ hAI
      have hgen : (A.map f).subgroupOf I ≤ offenderSubgroup (σ.comp I.subtype) :=
        le_iSup_of_le _ (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)
      exact (map_subgroupOf_eq_of_le hAI).symm.le.trans (map_mono hgen)
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := hI x.property
  exact (show y = x from Subtype.ext hxy) ▸ hy

/-- The faithful action of the actual Thompson image on U is best-generated. -/
theorem thompson_image_internal_generated (S U : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U] (hUS : U ≤ S)
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) :
    offenderSubgroup
      ((Representation.NormalElementaryQuotient.representation U f hf hker).comp
        ((elementaryAbelianMaxJ S).map f).subtype) = ⊤ :=
  thompson_image_generated_of_maximum_images_best S f _
    (fun A hA hne => maximum_image_isBestOffender S U A hUS hA f hf hker hne)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
