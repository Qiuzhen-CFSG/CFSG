module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The normal closure in a plane action

A two-subgroup whose image is a transposition in S₃ normally generates
its parabolic supplement, provided the action kernel normalizes it and
the supplement has a two-group kernel. Recovering the supplement's
p-residual proves its ambient normality. The kernel on the product is
derived from the disjoint cubic and two-group images.

This is the group-theoretic step of Aschbacher–Smith 13.3.15(1–4),
combined manuscript of 1 March 2004, printed pp.893–894. Its geometric
application uses the actual action of N_G(V₂) on V₂, not an abstract
replacement of the ambient local group.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- A complement to the kernel contains every conjugate of Q if the kernel
normalizes Q. The complement need not be normal. -/
theorem conjugateSpan_le_of_image_cover {H : Type*} [Group H]
    (f : G →* H) (Q J : Subgroup G) (hQ : Q ≤ J)
    (himage : f.range ≤ J.map f) (hk : f.ker ≤ normalizer (Q : Set G)) :
    conjugateSpanBy Q ⊤ ≤ J := by
  apply (closure_le _).mpr
  rintro _ ⟨g, _, q, hq, rfl⟩
  obtain ⟨j, hj, he⟩ := himage (show f g ∈ f.range from ⟨g, rfl⟩)
  have hker : j⁻¹ * g ∈ f.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  have hq' := (mem_normalizer_iff.mp (hk hker) q).mp hq
  have hh := J.mul_mem (J.mul_mem hj (hQ hq')) (J.inv_mem hj)
  have heq : j * (j⁻¹ * g * q * (j⁻¹ * g)⁻¹) * j⁻¹ = g * q * g⁻¹ := by group
  rwa [heq] at hh

private theorem permThree_conjugate_product (t : Equiv.Perm (Fin 3))
    (ht : t ^ 2 = 1) (hne : t ≠ 1) (x : Equiv.Perm (Fin 3)) :
    ∃ a b : Equiv.Perm (Fin 3),
      x = 1 ∨ x = a * t * a⁻¹ ∨ x = (a * t * a⁻¹) * (b * t * b⁻¹) := by
  revert x hne ht t
  decide +kernel

/-- Every nontrivial two-subgroup normally generates S3. -/
theorem permThree_conjugateSpan_eq_top (Q : Subgroup (Equiv.Perm (Fin 3)))
    (hq : Nat.card Q = 2) : conjugateSpanBy Q ⊤ = ⊤ := by
  have hneQ : Q ≠ ⊥ := by intro he; simp [he] at hq
  obtain ⟨t, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hneQ
  have ht := t.property
  have hne' : (t : Equiv.Perm (Fin 3)) ≠ 1 := fun he => hne (Subtype.ext he)
  have ht2 : (t : Equiv.Perm (Fin 3)) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨t, ht⟩ : Q))
    rw [hq] at h
    exact congrArg Subtype.val h
  apply top_unique
  intro x _
  obtain ⟨a, b, hx | hx | hx⟩ := permThree_conjugate_product t ht2 hne' x
  · rw [hx]; exact one_mem _
  · rw [hx]; exact subset_closure ⟨a, mem_top _, t, ht, rfl⟩
  · rw [hx]
    exact mul_mem (subset_closure ⟨a, mem_top _, t, ht, rfl⟩)
      (subset_closure ⟨b, mem_top _, t, ht, rfl⟩)

/-- A cubic image together with a two-element image fills S3. -/
theorem permThree_join_image_eq_top
    (f : G →* Equiv.Perm (Fin 3)) (X Q : Subgroup G)
    (hx : Nat.card (X.map f) = 3) (hq : Nat.card (Q.map f) = 2) :
    (X ⊔ Q).map f = ⊤ := by
  let J := (X ⊔ Q).map f
  have hd3 : 3 ∣ Nat.card J := by
    simpa only [hx] using card_dvd_of_le (map_mono (f := f) (show X ≤ X ⊔ Q from le_sup_left))
  have hd2 : 2 ∣ Nat.card J := by
    simpa only [hq] using card_dvd_of_le (map_mono (f := f) (show Q ≤ X ⊔ Q from le_sup_right))
  have hd6 : 6 ∣ Nat.card J :=
    (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd hd2 hd3
  apply eq_top_of_card_eq
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hp := Nat.card_pos (α := J)
  exact le_antisymm J.card_le_card_group (hc ▸ Nat.le_of_dvd hp hd6)

/-- A kernel on the normalized product is still a two-group. The odd and
 even quotient images intersect trivially, so its odd-factor part is in
 the original kernel. -/
theorem join_inf_ker_isPGroup_of_disjoint_images {H : Type*} [Group H]
    (f : G →* H) (X Q : Subgroup G)
    (hn : Q ≤ normalizer (X : Set G))
    (hx : IsPGroup 2 (X ⊓ f.ker : Subgroup G)) (hq : IsPGroup 2 Q)
    (hd : Disjoint (X.map f) (Q.map f)) :
    IsPGroup 2 ((X ⊔ Q) ⊓ f.ker : Subgroup G) := by
  have hnorm : Q ≤ normalizer ((X ⊓ f.ker : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro q hq x hx
    exact ⟨le_normalizer_iff.mp hn q hq x hx.1,
      (inferInstance : f.ker.Normal).conj_mem x hx.2 q⟩
  apply (hx.to_sup_of_normal_left' hq hnorm).to_le
  intro z hz
  have hprod : z ∈ (X : Set G) * (Q : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left X Q hn]
    exact hz.1
  obtain ⟨x, hx, q, hq, rfl⟩ := hprod
  have he : f x = (f q)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact (map_mul f x q).symm.trans hz.2
  have hxf : f x ∈ X.map f ⊓ Q.map f :=
    ⟨mem_map_of_mem f hx, he ▸ (Q.map f).inv_mem (mem_map_of_mem f hq)⟩
  have hxo : f x = 1 := hd.le_bot hxf
  exact (X ⊓ f.ker ⊔ Q).mul_mem (mem_sup_left ⟨hx, hxo⟩) (mem_sup_right hq)

/-- A faithful-on-the-quotient parabolic supplement turns the normal closure
of the original two-subgroup into the literal product. -/
theorem conjugateSpan_eq_join_of_permThree
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (X Q : Subgroup G) (hX : IsPPerfect 2 X)
    (hcover : (X ⊔ Q).map f = ⊤)
    (hq : Nat.card (Q.map f) = 2)
    (hk : IsPGroup 2 ((X ⊔ Q) ⊓ f.ker : Subgroup G))
    (hker : f.ker ≤ normalizer (Q : Set G)) :
    conjugateSpanBy Q ⊤ = X ⊔ Q := by
  let I := conjugateSpanBy Q ⊤
  let J := X ⊔ Q
  have hIJ : I ≤ J := conjugateSpan_le_of_image_cover f Q J le_sup_right
    (by rw [hcover]; exact le_top) hker
  have hIn : I.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_unique (le_normalizer_conjugateSpanBy Q ⊤)
  let := hIn
  have hmap : I.map f = ⊤ := by
    change (conjugateSpanBy Q ⊤).map f = ⊤
    rw [map_conjugateSpanBy, ← MonoidHom.range_eq_map, f.range_eq_top_of_surjective hf]
    exact permThree_conjugateSpan_eq_top _ hq
  have hjoin : X ≤ I ⊔ (J ⊓ f.ker) := by
    intro x hx
    obtain ⟨i, hi, he⟩ := (show f x ∈ I.map f by rw [hmap]; trivial)
    have hkx : i⁻¹ * x ∈ J ⊓ f.ker := by
      refine ⟨J.mul_mem (J.inv_mem (hIJ hi)) (mem_sup_left hx), ?_⟩
      change f (i⁻¹ * x) = 1
      simp only [map_mul, map_inv, he, inv_mul_cancel]
    have hh := (I ⊔ (J ⊓ f.ker)).mul_mem (mem_sup_left hi) (mem_sup_right hkx)
    simpa only [mul_inv_cancel_left] using hh
  have hXI : X ≤ I := le_normal_of_isPPerfect_of_le_sup_pGroup X I (J ⊓ f.ker) hX hk hjoin
  exact le_antisymm hIJ (sup_le hXI (le_conjugateSpanBy Q ⊤))

/-- The residual of this actual normal closure is the original parabolic,
so the full ambient group normalizes it. -/
theorem normalizes_parabolic_of_permThree
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (X Q : Subgroup G) (hX : IsPPerfect 2 X) (hQ : IsPGroup 2 Q)
    (hn : Q ≤ normalizer (X : Set G))
    (hcover : (X ⊔ Q).map f = ⊤)
    (hq : Nat.card (Q.map f) = 2)
    (hk : IsPGroup 2 ((X ⊔ Q) ⊓ f.ker : Subgroup G))
    (hker : f.ker ≤ normalizer (Q : Set G)) : X.Normal := by
  have he := conjugateSpan_eq_join_of_permThree f hf X Q hX hcover hq hk hker
  have hJ : (X ⊔ Q).Normal := by
    rw [← he]
    apply normalizer_eq_top_iff.mp
    exact top_unique (le_normalizer_conjugateSpanBy Q ⊤)
  let := hJ
  have hx := embedded_pResidual_join_pGroup X Q hX hQ hn
  rw [← hx]
  infer_instance

/-- The kernel on the actual supplement is its two-core, with its original
quotient map retained. -/
theorem product_twoCore_of_permThree [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (J : Subgroup G)
    (hcover : J.map f = ⊤) (hk : IsPGroup 2 (J ⊓ f.ker : Subgroup G)) :
    J.pCoreIn 2 = J ⊓ f.ker ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) := by
  let φ := f.comp J.subtype
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨j,hj,he⟩ := (show x ∈ J.map f by rw [hcover]; trivial)
    exact ⟨⟨j,hj⟩,he⟩
  have heker : φ.ker = (J ⊓ f.ker).subgroupOf J := by
    ext j
    exact ⟨fun h => ⟨j.property,h⟩, fun h => h.2⟩
  have hkφ : IsPGroup 2 φ.ker := by rw [heker]; exact hk.comap_subtype
  have he := ker_eq_twoCore_of_surjective_perm_three φ hφ hkφ
  constructor
  · change (pCore 2 J).map J.subtype = J ⊓ f.ker
    rw [← he,heker,map_subgroupOf_eq_of_le inf_le_left]
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq he.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end Subgroup
