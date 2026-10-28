module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FixedKernel
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates
public import Theory.SpecificGroups.Suzuki.BorelPairGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.Torus

/-!
# Actual rank-one inversion and the source Cartan kernel

The root-reflection marking is first replaced by an involution in the same
root-generated subgroup. Its image lies outside the entire faithful Borel.
The linear and positive Suzuki two-point geometry then invert the image of
H. At Sz(2), the full Sylow normalizer has order four, so the odd Cartan
image is trivial. Thus C_H(s_i) is exactly H ∩ K_i for either source
rank-one family, including the nonperfect binary groups.

This discharges the rank-one inversion premise in FixedKernel from actual
natural quotient markings. It retains the same Q, H and full quotient
Borel. Source: Fong–Seitz I, proof of (6H)(a), p.51; the earlier reflection
choice is on p.26. Pairing and equality of the two fields are not assumed
or proved here. OriginalCartan applies these results to the literal source.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.Converse BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open BenderSuzuki.PFchapter1section1 BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

private theorem inversion_of_pair_model {M : Type*} [Group M]
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M)
    (B : Subgroup M) (hB : (quotientBorel Q i).map μ.toMonoidHom = B)
    (s : RootReflection Q split i)
    (hpair : ∀ t : M, IsInvolution t → t ∉ B →
      ∀ x ∈ B, t*x*t⁻¹ ∈ B → t⁻¹*x*t = x⁻¹)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    cartanPanelMap Q i (simpleCartanAction Q split i h) = (cartanPanelMap Q i h)⁻¹ := by
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
  have ht : IsInvolution t := ⟨fun he => htB (he ▸ B.one_mem),ht2⟩
  have hhB (a : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
      μ (cartanPanelMap Q i a) ∈ B := by
    rw [← hB]
    exact mem_map_of_mem _ (cartanPanelMap_mem_borel Q i a)
  have hconj : t * μ (cartanPanelMap Q i h) * t⁻¹ ∈ B := by
    have he := congrArg μ (cartanPanelMap_reflection Q split i r h)
    simp only [map_mul, map_inv] at he
    change μ (cartanPanelMap Q i (simpleCartanAction Q split i h)) =
      t⁻¹ * μ (cartanPanelMap Q i h) * t at he
    rw [ht.inv_eq_self] at he
    rw [ht.inv_eq_self, ← he]
    exact hhB _
  apply μ.injective
  rw [cartanPanelMap_reflection Q split i r h, map_mul, map_mul, map_inv, map_inv]
  exact hpair t ht htB _ (hhB h) hconj

/-- Natural linear rank-one markings force the source Cartan image to be inverted. -/
theorem linear_cartan_inversion (n : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    cartanPanelMap Q i (simpleCartanAction Q split i h) = (cartanPanelMap Q i h)⁻¹ := by
  apply inversion_of_pair_model Q split i μ _ hB s ?_ h
  intro t ht htB x hx htx
  apply BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.twoPoint_inverted
    (MulEquiv.refl (PSL2BinaryMatrixGroup n)) T ht htB
  refine ⟨hx,?_⟩
  exact (BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.mem_rightConjugate _ _ _).mpr htx

/-- The small Suzuki panel normalizer has order four, including its entire Borel. -/
theorem suzuki_binary_normalizer_card :
    Nat.card (normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0))) = 4 := by
  have hi := suzuki_normalizer_index 0 (matrixRootSylow 0)
  have he : (matrixRootSylow 0 : Set (SuzukiMatrixGroup 0)) = SuzukiRootSubgroup 0 :=
    congrArg (fun A : Subgroup (SuzukiMatrixGroup 0) => (A : Set (SuzukiMatrixGroup 0)))
      (matrixRootSylow_carrier 0)
  rw [he] at hi
  have hcT : Nat.card (matrixRootSylow 0) = 4 := by
    exact (Nat.card_congr (MulEquiv.subgroupCongr (matrixRootSylow_carrier 0)).toEquiv).trans
      (by simpa using matrixRoot_card 0)
  rw [hcT] at hi
  have hc := (normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0))).card_mul_index
  rw [hi, suzukiZero_card] at hc
  omega

include split in
/-- At Sz(2) the odd source Cartan has trivial image, without using simplicity. -/
theorem binary_suzuki_cartan_image (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) : cartanPanelMap Q i h = 1 := by
  let f := μ.toMonoidHom.comp (cartanPanelMap Q i)
  have hf : f.range ≤ normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)) := by
    rintro x ⟨a,rfl⟩
    rw [← hB]
    exact mem_map_of_mem _ (cartanPanelMap_mem_borel Q i a)
  have hd := card_dvd_of_le hf
  rw [suzuki_binary_normalizer_card] at hd
  have hod := split.odd.of_dvd_right (card_range_dvd f)
  have hone : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes (hod.symm.pow_right 2) dvd_rfl hd
  have hz := (Subgroup.card_eq_one.mp hone).le (show f h ∈ f.range from ⟨h,rfl⟩)
  apply μ.injective
  exact (mem_bot.mp hz).trans (map_one μ).symm

/-- The source Suzuki Cartan action is inverted for every parameter m ≥ 0. -/
theorem suzuki_cartan_inversion (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    cartanPanelMap Q i (simpleCartanAction Q split i h) = (cartanPanelMap Q i h)⁻¹ := by
  by_cases hm : m = 0
  · subst m
    rw [binary_suzuki_cartan_image Q split i μ hB,
      binary_suzuki_cartan_image Q split i μ hB, inv_one]
  · have hmpos := Nat.pos_of_ne_zero hm
    rw [suzukiRootSubgroup_normalizer m hmpos] at hB
    apply inversion_of_pair_model Q split i μ _ hB s ?_ h
    intro t ht htB x hx htx
    apply suzukiBorel_pair_inverted m hmpos t ht htB x
    refine ⟨hx,?_⟩
    exact (BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.mem_rightConjugate _ _ _).mpr htx

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

theorem linear_reflectionFixed_eq_kernel (n : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) :
    reflectionFixed Q split i = (cartanPanelMap Q i).ker :=
  reflectionFixed_eq_kernel Q split i s (linear_cartan_inversion Q split i n μ T hB s)

theorem suzuki_reflectionFixed_eq_kernel (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) :
    reflectionFixed Q split i = (cartanPanelMap Q i).ker :=
  reflectionFixed_eq_kernel Q split i s (suzuki_cartan_inversion Q split i m μ hB s)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
