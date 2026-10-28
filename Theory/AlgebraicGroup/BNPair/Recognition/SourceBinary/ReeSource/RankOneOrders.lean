module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RankOneCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanImage

/-!
# Orders of the actual source Cartan images

The natural rank-one pair geometry identifies each faithful two-point
subgroup and gives its field-unit order. CartanImage removes the original
two-part and proves that H maps onto that whole subgroup. Thus the two
actual images have orders 2^n−1 and 2^(2m+1)−1. The joint kernel theorem
then bounds H by their product without identifying the two parameters.
At n=1,m=0 this proves that the whole source Cartan is trivial.

Source: Fong–Seitz I, proof of (6H)(a), p.51. The mutual-divisibility
argument forcing n=2m+1, the cross-root actions, and the remainder of
(6H) still require proof. OriginalCartan applies these statements to the
same original/geometric quotient, preserving both natural panel markings.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

private theorem model_reflection_involution {M : Type*} [Group M]
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M)
    (B : Subgroup M) (hB : (quotientBorel Q i).map μ.toMonoidHom = B)
    (s : RootReflection Q split i) :
    let t := μ (QuotientGroup.mk' (panelKernel Q i)
      (rootReflectionEndpoint Q split i (involutoryRootReflection Q split i s)))
    IsInvolution t ∧ t ∉ B := by
  let r := involutoryRootReflection Q split i s
  let q := QuotientGroup.mk' (panelKernel Q i)
  let t := μ (q (rootReflectionEndpoint Q split i r))
  have htB : t ∉ B := by
    intro ht
    rw [← hB, mem_map_equiv] at ht
    have hc : q (rootReflectionEndpoint Q split i r) ∈ quotientBorel Q i := by
      simpa only [t, MulEquiv.symm_apply_apply] using ht
    exact rootReflectionProjection_not_mem_borel Q split i r hc
  have ht2 : t^2 = 1 := by
    have hr2 : (rootReflectionEndpoint Q split i r)^2 = 1 :=
      Subtype.ext (involutoryRootReflection_sq Q split i s)
    change (μ (q (rootReflectionEndpoint Q split i r)))^2 = 1
    rw [← map_pow, ← map_pow, hr2, map_one, map_one]
  change IsInvolution t ∧ t ∉ B
  exact ⟨⟨fun he => htB (he ▸ B.one_mem),ht2⟩,htB⟩

private theorem rightConjugate_eq_native {M : Type*} [Group M] (B : Subgroup M) (t : M) :
    rightConjugate B t = BenderSuzuki.PFchapter1section1.rightConjugate B t := by
  ext x
  exact (BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.mem_rightConjugate B t x).symm

/-- The literal linear two-point subgroup has its natural field-unit order. -/
theorem linear_panelCartanPair_card (n : ℕ) (hn : 0 < n)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) :
    Nat.card (panelCartanPair Q split i (involutoryRootReflection Q split i s)) = 2^n-1 := by
  obtain ⟨ht,htB⟩ := model_reflection_involution Q split i μ _ hB s
  rw [Nat.card_congr (panelCartanPairEquiv Q split i μ _ hB
    (involutoryRootReflection Q split i s)).toEquiv, rightConjugate_eq_native]
  exact (BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.twoPoint_cyclic_card hn
    (MulEquiv.refl (PSL2BinaryMatrixGroup n)) T ht htB).2

/-- Actual image order, not merely the order of an unrelated model torus. -/
theorem linear_cartanImage_card (n : ℕ) (hn : 0 < n)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) : Nat.card (cartanPanelMap Q i).range = 2^n-1 := by
  have hcard := linear_panelCartanPair_card Q split i n hn μ T hB s
  have hodd : Nat.Coprime 2 (Nat.card (panelCartanPair Q split i
      (involutoryRootReflection Q split i s))) := by
    rw [hcard]
    exact (Nat.Even.sub_odd (pow_pos (by decide : 0 < (2 : ℕ)) n)
      (even_two.pow_of_ne_zero hn.ne') odd_one).coprime_two_left
  rw [cartanPanelMap_range_eq_pair Q split i _ hodd, hcard]

/-- The actual positive-parameter Suzuki two-point subgroup has order q−1. -/
theorem suzuki_panelCartanPair_card (m : ℕ) (hm : 0 < m)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) :
    Nat.card (panelCartanPair Q split i (involutoryRootReflection Q split i s)) =
      2^(2*m+1)-1 := by
  rw [suzukiRootSubgroup_normalizer m hm] at hB
  obtain ⟨ht,htB⟩ := model_reflection_involution Q split i μ _ hB s
  rw [Nat.card_congr (panelCartanPairEquiv Q split i μ _ hB
    (involutoryRootReflection Q split i s)).toEquiv, rightConjugate_eq_native]
  exact suzukiBorel_pair_card m hm _ ht htB

/-- All-parameter Suzuki Cartan-image order, with Sz(2) handled separately. -/
theorem suzuki_cartanImage_card (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) : Nat.card (cartanPanelMap Q i).range = 2^(2*m+1)-1 := by
  by_cases hm : m = 0
  · subst m
    have hbot : (cartanPanelMap Q i).range = ⊥ := by
      apply eq_bot_iff.mpr
      rintro x ⟨h,rfl⟩
      exact binary_suzuki_cartan_image Q split i μ hB h
    rw [hbot, Subgroup.card_bot]
    norm_num
  · have hmpos := Nat.pos_of_ne_zero hm
    have hcard := suzuki_panelCartanPair_card Q split i m hmpos μ hB s
    have hodd : Nat.Coprime 2 (Nat.card (panelCartanPair Q split i
        (involutoryRootReflection Q split i s))) := by
      rw [hcard]
      exact (Nat.Even.sub_odd (pow_pos (by decide : 0 < (2 : ℕ)) (2*m+1))
        (even_two.pow_of_ne_zero (by omega)) odd_one).coprime_two_left
    rw [cartanPanelMap_range_eq_pair Q split i _ hodd, hcard]

/-- The product-order divisibility in the Ree source argument, before the two
field parameters have been proved equal. -/
theorem ree_cartan_card_dvd (n : ℕ) (hn : 0 < n) (m : ℕ)
    (μ₀ : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB₀ : (quotientBorel Q 0).map μ₀.toMonoidHom = normalizer (T : Set _))
    (μ₁ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB₁ : (quotientBorel Q 1).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : ∀ i, RootReflection Q split i) (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ∣ (2^n-1) * (2^(2*m+1)-1) := by
  have hd := cartan_card_dvd_product_images Q split s hcore
  rw [linear_cartanImage_card Q split 0 n hn μ₀ T hB₀ (s 0),
    suzuki_cartanImage_card Q split 1 m μ₁ hB₁ (s 1)] at hd
  exact hd

/-- In the genuine binary pair, the whole source Cartan is trivial. -/
theorem binary_ree_cartan_eq_bot
    (μ₀ : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup 1)
    (T : Sylow 2 (PSL2BinaryMatrixGroup 1))
    (hB₀ : (quotientBorel Q 0).map μ₀.toMonoidHom = normalizer (T : Set _))
    (μ₁ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB₁ : (quotientBorel Q 1).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (s : ∀ i, RootReflection Q split i) (hcore : Q.tits.B.normalCore = ⊥) :
    Q.tits.B ⊓ Q.tits.N = ⊥ := by
  apply Subgroup.card_eq_one.mp
  have hd := ree_cartan_card_dvd Q split 1 (by decide) 0 μ₀ T hB₀ μ₁ hB₁ s hcore
  simpa using hd

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
