module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CommonFieldArithmetic

/-!
# Common field degree and the exact two-factor source Cartan

On the same octagonal marked quotient, the perpendicular linear and Suzuki
root actions force both field-unit divisibilities. Their orders determine
the equality n=2m+1. Each actual panel kernel then has order q-1; the
trivial joint kernel and counting make multiplication an isomorphism from
their direct product onto the entire Cartan.

The natural PSL2/Suzuki panel markings, their root-group reflection choices,
and the oddness of the linear degree are explicit preceding inputs. This
module derives the action, divisibility, equality, and product statements;
it does not select those rank-one families or prove the parameter restriction
from the unreduced geometry. Nor does it synchronize the later module twists.

Source: Fong--Seitz I (1973), proof of (6H)(a), printed p.51, with the
odd-degree restriction cited there from (1J). OriginalCommonField transports
this result through both original endpoint maps and the full Borel marking.
The case m=0 gives the trivial Cartan of the full binary source quotient.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (quotientBorel Q 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (quotientBorel Q 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (s : ∀ i, RootReflection Q split i) (hcore : Q.tits.B.normalCore = ⊥)

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- The linear perpendicular-root action yields the first source divisibility. -/
theorem linear_fieldUnit_dvd_suzuki : 2^n-1 ∣ 2^(2*m+1)-1 := by
  let w := Q.simple 1*Q.simple 0*Q.simple 1
  let r := involutoryRootReflection Q split 0 (s 0)
  have hc := linear_perpendicular_reflection_centralizes Q split 0 n μ₀ T hB₀ hm hn 1 (by decide) (s 0)
  have hleft := rootAction_card_dvd_fixed Q split 0 0 w r hc
  rw [linear_cartanImage_card Q split 0 n hn.pos μ₀ T hB₀ (s 0),
    linear_reflectionFixed_eq_kernel Q split 0 n μ₀ T hB₀ (s 0)] at hleft
  have hright := panelKernel_card_dvd_other Q split 0 1 (by decide) s hcore
  rw [suzuki_cartanImage_card Q split 1 m μ₁ hB₁ (s 1)] at hright
  exact hleft.trans hright

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- The Suzuki Frattini action yields the reverse source divisibility,
with the trivial field-unit group retained at m=0. -/
theorem suzuki_fieldUnit_dvd_linear : 2^(2*m+1)-1 ∣ 2^n-1 := by
  let w := Q.simple 0*Q.simple 1*Q.simple 0
  have hcompat := suzuki_perpendicular_action_eq Q split 1 m μ₁ hB₁ hm 0 (by decide) (s 1)
  have hleft := rootAction_card_dvd_fixed_of_compatible Q split 1 1 w hcompat
  rw [suzuki_cartanImage_card Q split 1 m μ₁ hB₁ (s 1),
    suzuki_reflectionFixed_eq_kernel Q split 1 m μ₁ hB₁ (s 1)] at hleft
  have hright := panelKernel_card_dvd_other Q split 1 0 (by decide) s hcore
  rw [linear_cartanImage_card Q split 0 n hn.pos μ₀ T hB₀ (s 0)] at hright
  exact hleft.trans hright

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- The two naturally marked rank-one fields on this octagonal quotient
have the same degree. No mutual-divisibility or root-action premise remains. -/
theorem ree_common_field_exponent : n = 2*m+1 :=
  common_field_exponent_of_mutual_dvd hn.pos (by omega)
    (linear_fieldUnit_dvd_suzuki Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore)
    (suzuki_fieldUnit_dvd_linear Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore)

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- Both actual panel kernels in H have the common field-unit order. -/
theorem ree_cartan_kernel_cards :
    Nat.card (cartanPanelMap Q 0).ker = 2^(2*m+1)-1 ∧
      Nat.card (cartanPanelMap Q 1).ker = 2^(2*m+1)-1 := by
  have he := ree_common_field_exponent Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore
  have h0 := rootAction_card_dvd_fixed Q split 0 0 (Q.simple 1*Q.simple 0*Q.simple 1)
    (involutoryRootReflection Q split 0 (s 0))
    (linear_perpendicular_reflection_centralizes Q split 0 n μ₀ T hB₀ hm hn 1 (by decide) (s 0))
  rw [linear_cartanImage_card Q split 0 n hn.pos μ₀ T hB₀ (s 0),
    linear_reflectionFixed_eq_kernel Q split 0 n μ₀ T hB₀ (s 0),he] at h0
  have h1 := rootAction_card_dvd_fixed_of_compatible Q split 1 1
    (Q.simple 0*Q.simple 1*Q.simple 0)
    (suzuki_perpendicular_action_eq Q split 1 m μ₁ hB₁ hm 0 (by decide) (s 1))
  rw [suzuki_cartanImage_card Q split 1 m μ₁ hB₁ (s 1),
    suzuki_reflectionFixed_eq_kernel Q split 1 m μ₁ hB₁ (s 1)] at h1
  have h0' := panelKernel_card_dvd_other Q split 0 1 (by decide) s hcore
  have h1' := panelKernel_card_dvd_other Q split 1 0 (by decide) s hcore
  rw [suzuki_cartanImage_card Q split 1 m μ₁ hB₁ (s 1)] at h0'
  rw [linear_cartanImage_card Q split 0 n hn.pos μ₀ T hB₀ (s 0),he] at h1'
  exact ⟨Nat.dvd_antisymm h0' h0,Nat.dvd_antisymm h1' h1⟩

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
theorem ree_cartan_card :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = (2^(2*m+1)-1)^2 := by
  have he := ree_common_field_exponent Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore
  have hk := (ree_cartan_kernel_cards Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore).1
  have hc := (cartanPanelMap Q 0).ker.card_mul_index
  rw [index_ker,hk,linear_cartanImage_card Q split 0 n hn.pos μ₀ T hB₀ (s 0),he,← pow_two] at hc
  exact hc.symm

private theorem perpendicular_kernel_of_card (i : Fin 2) (w : Weyl Q)
    (hcompat : ∀ h, rootAction Q split i w (simpleCartanAction Q split i h) =
      rootAction Q split i w h)
    (a : ℕ) (ha : 0 < a)
    (hH : Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = a*a)
    (hr : Nat.card (rootAction Q split i w).range = a)
    (hi : Nat.card (reflectionInverted Q split i) = a) :
    (rootAction Q split i w).ker = reflectionInverted Q split i := by
  have hle : reflectionInverted Q split i ≤ (rootAction Q split i w).ker := by
    intro b hb
    obtain ⟨c,hc⟩ := (reflectionDisplacement_range Q split i).ge hb
    rw [← hc]
    change rootAction Q split i w (c⁻¹*simpleCartanAction Q split i c) = 1
    rw [map_mul,map_inv,hcompat,inv_mul_cancel]
  have hc := (rootAction Q split i w).ker.card_mul_index
  rw [index_ker,hr,hH] at hc
  have hk : Nat.card (rootAction Q split i w).ker = a := Nat.eq_of_mul_eq_mul_right ha hc
  exact (eq_of_le_of_card_ge hle (by rw [hk,hi])).symm

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- The Cartan kernel on each perpendicular root is exactly the inverted
factor of its original simple reflection. This is the first independent-root
kernel identification following (6H)(a) on printed p.51. -/
theorem ree_perpendicular_kernels :
    (rootAction Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)).ker = reflectionInverted Q split 0 ∧
      (rootAction Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).ker = reflectionInverted Q split 1 := by
  have he := ree_common_field_exponent Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore
  have hH := ree_cartan_card Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore
  rw [pow_two] at hH
  have hq : 0 < 2^(2*m+1)-1 := by
    have : 1 < (2:ℕ)^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
    omega
  constructor
  · apply perpendicular_kernel_of_card Q split 0 _
      (rootAction_reflection_eq Q split 0 0 _ (involutoryRootReflection Q split 0 (s 0))
        (linear_perpendicular_reflection_centralizes Q split 0 n μ₀ T hB₀ hm hn 1 (by decide) (s 0)))
      _ hq hH
    · rw [Nat.card_congr (rootActionImageEquiv Q split 0 _).toEquiv,
        linear_cartanImage_card Q split 0 n hn.pos μ₀ T hB₀ (s 0),he]
    · rw [linear_inverted_card Q split 0 n hn.pos μ₀ T hB₀ (s 0),he]
  · apply perpendicular_kernel_of_card Q split 1 _
      (suzuki_perpendicular_action_eq Q split 1 m μ₁ hB₁ hm 0 (by decide) (s 1)) _ hq hH
    · rw [Nat.card_congr (rootActionImageEquiv Q split 1 _).toEquiv,
        suzuki_cartanImage_card Q split 1 m μ₁ hB₁ (s 1)]
    · exact suzuki_inverted_card Q split 1 m μ₁ hB₁ (s 1)

open scoped IsMulCommutative

/-- Multiplication of the two exact panel kernels inside the full Cartan. -/
def cartanKernelProductMap : (cartanPanelMap Q 0).ker × (cartanPanelMap Q 1).ker →*
    (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := by
  let := split.abelian
  exact {
    toFun := fun p => p.1.val*p.2.val
    map_one' := one_mul _
    map_mul' := fun x y => by
      change (_*_) * (_*_) = (_*_) * (_*_)
      ac_rfl
  }

include s hcore in
theorem cartanKernelProductMap_injective : Function.Injective (cartanKernelProductMap Q split) := by
  have hd : Disjoint (cartanPanelMap Q 0).ker (cartanPanelMap Q 1).ker := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro h hh
    apply (cartanPanelPair_injective Q split s hcore)
    have h0 : cartanPanelMap Q 0 h = 1 := hh.1
    have h1 : cartanPanelMap Q 1 h = 1 := hh.2
    exact Prod.ext (h0.trans (map_one _).symm) (h1.trans (map_one _).symm)
  exact mul_injective_of_disjoint hd

/-- The source direct product in (6H)(a), with the actual two kernels and
actual multiplication map. All order and surjectivity premises are proved. -/
def reeCartanEquiv :
    (cartanPanelMap Q 0).ker × (cartanPanelMap Q 1).ker ≃*
      (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  MulEquiv.ofBijective (cartanKernelProductMap Q split) (by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    refine ⟨cartanKernelProductMap_injective Q split s hcore,?_⟩
    obtain ⟨h0,h1⟩ := ree_cartan_kernel_cards Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore
    rw [Nat.card_prod,h0,h1,ree_cartan_card Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore,pow_two])

@[simp] theorem reeCartanEquiv_apply (a : (cartanPanelMap Q 0).ker) (b : (cartanPanelMap Q 1).ker) :
    (reeCartanEquiv Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore (a,b) : X ⧸ Q.D) =
      (a.val : X ⧸ Q.D)*b.val := rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
