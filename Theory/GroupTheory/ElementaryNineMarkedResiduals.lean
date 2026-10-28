module

public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.PGroupCore
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Marked residual lifts over an elementary group of order nine

Suppose an automorphism fixes one marked cubic image and inverts the other.
For an invariant subgroup, writing `y = a * b` gives
`q(y)⁻¹ * q(τ(y)) = q(b)`, since `q(b)` has exponent three. Thus its image
splits into its intersections with the two marked lines. Each intersection is
trivial or the whole line, so a nonzero proper image is one marked line.

A two-perfect subgroup normalized by the two-kernel is the embedded
two-residual of its product with that kernel. This both proves normality when
the quotient is abelian and makes equality of quotient images lift uniquely.
Two-perfectness also rules out a trivial image, and, in a two-perfect ambient
group, a full image for a proper subgroup.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.877–878; proof of 13.7.5(7),
p.938; proof of 13.8.20, p.955 (combined manuscript of 1 March 2004).
-/

open Subgroup
namespace Theory.GroupTheory.ElementaryNineMarkedResiduals
variable {D E : Type*} [Group D] [Group E]

/-- A two-perfect lift normalized by the two-kernel is normal over an abelian image. -/
public theorem residual_lift_normal [IsMulCommutative E] (q : D →* E) (hQ : IsPGroup 2 q.ker)
    (Y : Subgroup D) (hY : IsPPerfect 2 Y)
    (hn : q.ker ≤ normalizer (Y : Set D)) : Y.Normal := by
  have he := embedded_pResidual_join_pGroup Y q.ker hY hQ hn
  have : (Y ⊔ q.ker).Normal := by
    rw [← comap_map_eq]
    infer_instance
  rw [← he]
  infer_instance

/-- Two-perfect lifts normalized by the two-kernel are determined by their images. -/
public theorem residual_lift_injective (q : D →* E) (hQ : IsPGroup 2 q.ker)
    (A B : Subgroup D) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hnA : q.ker ≤ normalizer (A : Set D))
    (hnB : q.ker ≤ normalizer (B : Set D))
    (he : A.map q = B.map q) : A = B := by
  have hj : A ⊔ q.ker = B ⊔ q.ker := by
    simpa only [comap_map_eq] using congrArg (fun S : Subgroup E => S.comap q) he
  rw [← embedded_pResidual_join_pGroup A q.ker hA hQ hnA,
    ← embedded_pResidual_join_pGroup B q.ker hB hQ hnB, hj]

/-- A nontrivial two-perfect subgroup cannot lie in a two-kernel. -/
public theorem image_ne_bot (q : D →* E) (hQ : IsPGroup 2 q.ker)
    (Y : Subgroup D) (hY : IsPPerfect 2 Y) (hne : Y ≠ ⊥) : Y.map q ≠ ⊥ := by
  intro he
  have hle := (map_eq_bot_iff Y).mp he
  have h := hY.hom_eq_one_of_isPGroup hQ (inclusion hle)
  apply hne
  apply le_bot_iff.mp
  intro y hy
  have he := congrArg (fun f : Y →* q.ker => (f ⟨y, hy⟩ : D)) h
  exact he

/-- A proper two-perfect lift normalized by the two-kernel cannot cover a two-perfect group. -/
public theorem image_ne_top [IsMulCommutative E] (q : D →* E) (hQ : IsPGroup 2 q.ker)
    (hD : IsPPerfect 2 D) (Y : Subgroup D) (hY : IsPPerfect 2 Y)
    (hn : q.ker ≤ normalizer (Y : Set D)) (hne : Y ≠ ⊤) : Y.map q ≠ ⊤ := by
  intro he
  have hj : Y ⊔ q.ker = ⊤ := by
    simpa only [comap_map_eq, comap_top] using congrArg (fun S : Subgroup E => S.comap q) he
  let _ := residual_lift_normal q hQ Y hY hn
  have hres := pResidual_eq_of_isPPerfect_sup Y q.ker hY hQ hj
  exact hne (hres.symm.trans ((pResidual_eq_top_iff 2 D).mpr hD))

private theorem prime_intersection (U S : Subgroup E) (hU : Nat.card U = 3) :
    S ⊓ U = ⊥ ∨ S ⊓ U = U := by
  let : Fact (Nat.card U).Prime := ⟨hU ▸ Nat.prime_three⟩
  have hh := (S.subgroupOf U).eq_bot_or_eq_top_of_prime_card
  have hh := hh.imp (congrArg (fun H : Subgroup U => H.map U.subtype))
    (congrArg (fun H : Subgroup U => H.map U.subtype))
  simpa only [subgroupOf_map_subtype, Subgroup.map_bot, ← MonoidHom.range_eq_map, range_subtype,
    inf_comm] using hh

private theorem image_splits (q : D →* E) (A B Y : Subgroup D) [A.Normal]
    (hgen : A ⊔ B = ⊤) (hB : Nat.card (B.map q) = 3) (τ : MulAut D)
    (hfix : ∀ a ∈ A, q (τ a) = q a)
    (hinv : ∀ b ∈ B, q (τ b) = (q b)⁻¹)
    (hY : ∀ y ∈ Y, τ y ∈ Y) :
    Y.map q = (Y.map q ⊓ A.map q) ⊔ (Y.map q ⊓ B.map q) := by
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp
    (show y ∈ A ⊔ B by rw [hgen]; trivial)
  have hby : q b ∈ B.map q := mem_map.mpr ⟨b, hb, rfl⟩
  have hb3 : q b ^ 3 = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨q b, hby⟩ : B.map q)))
    simpa only [hB, coe_pow, coe_one] using h
  have hb2 : q b * q b = (q b)⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_succ, pow_zero, one_mul] using hb3)
  have hproj : (q y)⁻¹ * q (τ y) = q b := by
    calc
      (q y)⁻¹ * q (τ y) = (q b * q b)⁻¹ := by
        rw [← hab, map_mul, map_mul, map_mul, hfix a ha, hinv b hb]
        group
      _ = q b := by rw [hb2, inv_inv]
  have hbY : q b ∈ Y.map q := by
    rw [← hproj]
    exact (Y.map q).mul_mem ((Y.map q).inv_mem (mem_map.mpr ⟨y, hy, rfl⟩))
      (mem_map.mpr ⟨τ y, hY y hy, rfl⟩)
  have haY : q a ∈ Y.map q := by
    have he : q a = q y * (q b)⁻¹ := by rw [← hab, map_mul]; group
    rw [he]
    exact (Y.map q).mul_mem (mem_map.mpr ⟨y, hy, rfl⟩) ((Y.map q).inv_mem hbY)
  rw [← hab, map_mul]
  exact ((Y.map q ⊓ A.map q) ⊔ (Y.map q ⊓ B.map q)).mul_mem
    ((show Y.map q ⊓ A.map q ≤ (Y.map q ⊓ A.map q) ⊔ (Y.map q ⊓ B.map q)
      from le_sup_left) ⟨haY, mem_map.mpr ⟨a, ha, rfl⟩⟩)
    ((show Y.map q ⊓ B.map q ≤ (Y.map q ⊓ A.map q) ⊔ (Y.map q ⊓ B.map q)
      from le_sup_right) ⟨hbY, hby⟩)

private theorem image_eq_marked (q : D →* E) (hq : Function.Surjective q)
    (A B Y : Subgroup D) [A.Normal]
    (hgen : A ⊔ B = ⊤) (hA : Nat.card (A.map q) = 3) (hB : Nat.card (B.map q) = 3)
    (τ : MulAut D) (hfix : ∀ a ∈ A, q (τ a) = q a)
    (hinv : ∀ b ∈ B, q (τ b) = (q b)⁻¹) (hY : ∀ y ∈ Y, τ y ∈ Y)
    (hne : Y.map q ≠ ⊥) (hproper : Y.map q ≠ ⊤) :
    Y.map q = A.map q ∨ Y.map q = B.map q := by
  have hs := image_splits q A B Y hgen hB τ hfix hinv hY
  have htop : A.map q ⊔ B.map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q hq]
  rcases prime_intersection (A.map q) (Y.map q) hA with ha | ha <;>
    rcases prime_intersection (B.map q) (Y.map q) hB with hb | hb
  · exact (hne (by simpa only [ha, hb, bot_sup_eq] using hs)).elim
  · exact Or.inr (by simpa only [ha, hb, bot_sup_eq] using hs)
  · exact Or.inl (by simpa only [ha, hb, sup_bot_eq] using hs)
  · exact (hproper (by simpa only [ha, hb, htop] using hs)).elim

private theorem eq_marked [IsMulCommutative E] (q : D →* E) (hq : Function.Surjective q)
    (hQ : IsPGroup 2 q.ker) (hD : IsPPerfect 2 D)
    (A B Y : Subgroup D) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hY : IsPPerfect 2 Y)
    (hnA : q.ker ≤ normalizer (A : Set D))
    (hnB : q.ker ≤ normalizer (B : Set D))
    (hnY : q.ker ≤ normalizer (Y : Set D))
    (hgen : A ⊔ B = ⊤) (hcA : Nat.card (A.map q) = 3) (hcB : Nat.card (B.map q) = 3)
    (τ : MulAut D) (hfix : ∀ a ∈ A, q (τ a) = q a)
    (hinv : ∀ b ∈ B, q (τ b) = (q b)⁻¹) (hτY : ∀ y ∈ Y, τ y ∈ Y)
    (hne : Y ≠ ⊥) (hproper : Y ≠ ⊤) : Y = A ∨ Y = B := by
  let _ := residual_lift_normal q hQ A hA hnA
  have him := image_eq_marked q hq A B Y hgen hcA hcB τ hfix hinv hτY
    (image_ne_bot q hQ Y hY hne) (image_ne_top q hQ hD Y hY hnY hproper)
  exact him.imp (residual_lift_injective q hQ Y A hY hA hnY hnA)
    (residual_lift_injective q hQ Y B hY hB hnY hnB)

/-- Relative to the actual elementary-nine quotient, every normalized two-perfect lift is normal. -/
public theorem normal_of_elementaryNine
    (e : D ⧸ pCore 2 D ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (Y : Subgroup D) (hY : IsPPerfect 2 Y)
    (hn : pCore 2 D ≤ normalizer (Y : Set D)) : Y.Normal := by
  let : IsMulCommutative (D ⧸ pCore 2 D) := .of_comm fun a b =>
    e.injective (by simp only [map_mul, mul_comm])
  refine residual_lift_normal (QuotientGroup.mk' (pCore 2 D)) ?_ Y hY ?_
  · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  · simpa only [QuotientGroup.ker_mk'] using hn

/-- The invariant nontrivial proper two-perfect lifts are the two marked cubic lifts. -/
public theorem eq_marked_of_elementaryNine
    (e : D ⧸ pCore 2 D ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hD : IsPPerfect 2 D) (A B Y : Subgroup D)
    (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B) (hY : IsPPerfect 2 Y)
    (hnA : pCore 2 D ≤ normalizer (A : Set D))
    (hnB : pCore 2 D ≤ normalizer (B : Set D))
    (hnY : pCore 2 D ≤ normalizer (Y : Set D))
    (hgen : A ⊔ B = ⊤)
    (hcA : Nat.card (A.map (QuotientGroup.mk' (pCore 2 D))) = 3)
    (hcB : Nat.card (B.map (QuotientGroup.mk' (pCore 2 D))) = 3)
    (τ : MulAut D)
    (hfix : ∀ a ∈ A, QuotientGroup.mk' (pCore 2 D) (τ a) = QuotientGroup.mk' (pCore 2 D) a)
    (hinv : ∀ b ∈ B, QuotientGroup.mk' (pCore 2 D) (τ b) = (QuotientGroup.mk' (pCore 2 D) b)⁻¹)
    (hτY : ∀ y ∈ Y, τ y ∈ Y) (hne : Y ≠ ⊥) (hproper : Y ≠ ⊤) :
    Y = A ∨ Y = B := by
  let : IsMulCommutative (D ⧸ pCore 2 D) := .of_comm fun a b =>
    e.injective (by simp only [map_mul, mul_comm])
  apply eq_marked (QuotientGroup.mk' (pCore 2 D))
    (QuotientGroup.mk'_surjective _) _ hD A B Y hA hB hY
    _ _ _ hgen hcA hcB τ hfix hinv hτY hne hproper
  · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  · simpa only [QuotientGroup.ker_mk'] using hnA
  · simpa only [QuotientGroup.ker_mk'] using hnB
  · simpa only [QuotientGroup.ker_mk'] using hnY
end Theory.GroupTheory.ElementaryNineMarkedResiduals
