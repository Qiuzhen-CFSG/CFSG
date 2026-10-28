module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeExtension
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeRotation
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CodeInputs

/-!
# Excluding an odd extension of the original code tensor pair

On the literal P/U, the actual pair image is D10 and its quintic rotation
is fixed-point free. The commuting residual cubic is also fixed-point free.
If an odd involution normalizes this same pair, the native full-kernel
cover transfers cubic inversion to P/U. A reflection twist centralizes
D10 and still inverts the cubic, giving fixed rank six, contrary to
four-divisibility for the fixed-point-free quintic action.

The extension theorem retains the original subgroups, sectionAction and
both intrinsic two-core kernels. Its Chapter12 application constructs
all its premises under the hypothetical normalization of the original
O²(I). Source: Aschbacher--Smith 8.2.8(6), printed p.719,
refs/quasithin.pdf. Native model attribution: LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open Normalizer.TensorRecognition Normalizer.SmallOvergroups
open MathieuCode.NormalizedShadowRows.CodeExtension
open scoped IsMulCommutative
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- An involution normalizing the actual D10 image and inverting its
commuting cubic contradicts the original twelve-dimensional code action. -/
theorem code_obstruction_of_normalized_cubic
    (I U : Subgroup G) [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    (ρ : Representation (ZMod 2) H (CoreSection I U))
    (D : Subgroup H) (e : D ≃* DihedralGroup 5) (x : D) (z t : H)
    (hx : orderOf x.val = 5) (ht : t ^ 2 = 1)
    (hn : t ∈ normalizer (D : Set H))
    (hDz : ∀ d : D, Commute d.val z)
    (hz3 : z ^ 3 = 1) (htz : t * z * t⁻¹ = z⁻¹)
    (hzfree : ∀ p, ρ z p = p → p = 0)
    (hxfree : ∀ p, ρ x.val p = p → p = 0)
    (hdim : Module.finrank (ZMod 2) (CoreSection I U) = 12) : False := by
  obtain ⟨v,s,hchoice,hs,hcentral⟩ := normalizing_involution_twist D e t ht hn
  have hinv : s * z * s⁻¹ = z⁻¹ := by
    rcases hchoice with rfl | rfl
    · exact htz
    · calc
        (t * v.val) * z * (t * v.val)⁻¹ = t * (v.val * z * v.val⁻¹) * t⁻¹ := by group
        _ = t * z * t⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr (hDz v).eq]
        _ = z⁻¹ := htz
  have hzInv : z⁻¹ = z ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [←pow_succ'] using hz3
  have hsz : s * z = z ^ 2 * s := by
    rw [hzInv] at hinv
    exact mul_inv_eq_iff_eq_mul.mp hinv
  have hd := CyclicFixedRank.twice_fixedRank_of_inverted_cubic ρ z s hz3 hs hsz hzfree
  rw [hdim] at hd
  have hfixed : Module.finrank (ZMod 2) (LinearMap.ker (ρ s - LinearMap.id)) = 6 := by omega
  exact code_fixed_rank_obstruction I U ρ x.val s hx (hcentral x) hxfree hfixed

/-- The full original product action cannot extend across an odd involution
normalizing the same I. The native cover and the quotient action retain
exactly the intrinsic two-core of R, so cubic inversion transfers between them. -/
theorem code_pair_odd_extension_impossible
    {R I V U N K : Subgroup G} {i : I}
    (hp : CodePairProductAction R I V U)
    (hnat : CodePairNaturalAction R I V U i)
    (hm : CodePairMultiplicityAction R I V U i)
    (hD : Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5))
    (hRN : R ≤ N) (hRK : R ≤ K) (hIK : I ≤ K)
    (hKP : K ≤ normalizer (I.pCoreIn 2 : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (p : R →* HexEvenAutomorphisms) (hpSurj : Function.Surjective p)
    (hpk : p.ker = pCore 2 R)
    (f : N →* HexAutomorphisms) (hf : ∀ r, f (inclusion hRN r) = (p r).val)
    (t : G) (htN : t ∈ N) (htK : t ∈ K)
    (htR : t ∈ normalizer (R : Set G)) (htI : t ∈ normalizer (I : Set G))
    (ht2 : t ^ 2 = 1) (htodd : hexSign (f ⟨t,htN⟩) = -1) : False := by
  obtain ⟨hYP,hYU,hUP,eR,z,hz,hzmark,hzc,hzfree,hzI⟩ := code_pair_cubic_actor hp hnat
  let := hUP
  obtain ⟨_,_,_,hEl,hcard,hker,hcore,hRker,hIker,_⟩ := hp
  let := hEl
  let P := I.pCoreIn 2
  let Q := P ⧸ U.subgroupOf P
  let σ : K →* MulAut Q := sectionAction K P U hKP hKU
  let σI : I →* MulAut Q := σ.comp (inclusion hIK)
  let σR : R →* MulAut Q := σ.comp (inclusion hRK)
  have hIker' : σI.ker = pCore 2 I := hIker
  have hRker' : σR.ker = pCore 2 R := hRker
  let D := σI.range
  obtain ⟨eD⟩ := hD
  let e : D ≃* DihedralGroup 5 :=
    (QuotientGroup.quotientKerEquivRange σI).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hIker').trans eD)
  obtain ⟨_,_,_,x,hx,hxq,hxfree⟩ := code_pair_quintic_rotation hm ⟨eD⟩
  let xD : D := ⟨σI x,⟨x,rfl⟩⟩
  let zK := σR z
  let tK := σ ⟨t,htK⟩
  have hxD : orderOf xD.val = 5 := by
    have hk : IsPGroup 2 σI.ker := hIker'.symm ▸ pCore_isPGroup
    exact (σI.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x (by rw [hx]; decide)).trans hx
  have ht : tK ^ 2 = 1 := by
    rw [←map_pow]
    have he : (⟨t,htK⟩ : K)^2 = 1 := Subtype.ext ht2
    rw [he,map_one]
  have htD : tK ∈ normalizer (D : Set (MulAut Q)) := by
    have he : (I.subgroupOf K).map σ = D := by
      ext y
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ⟨⟨a,ha⟩,rfl⟩
      · rintro ⟨a,rfl⟩
        exact ⟨inclusion hIK a,a.property,rfl⟩
    rw [←he]
    apply le_normalizer_map σ
    refine ⟨⟨t,htK⟩,?_,rfl⟩
    exact le_normalizer_comap K.subtype htI
  have hDz (d : D) : Commute d.val zK := by
    obtain ⟨a,ha⟩ := d.property
    change σI a = d.val at ha
    rw [←ha]
    exact (hzI a).symm
  have hz3 : zK^3 = 1 := by
    rw [←map_pow,←hz,pow_orderOf_eq_one,map_one]
  have hinv : tK * zK * tK⁻¹ = zK⁻¹ :=
    odd_inverts_central_quotient R N K hRN hRK p hpSurj hpk f hf σ hRker'.ge
      t htN htK htR htodd z hzc
  let ρ : Representation (ZMod 2) (MulAut Q) (Additive Q) := {
    toFun a := a.toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro v; rfl
    map_mul' a b := by apply LinearMap.ext; intro v; rfl }
  have hdim : Module.finrank (ZMod 2) (CoreSection I U) = 12 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    rw [Nat.card_zmod] at hc
    have hh : (2 : ℕ)^12 = 2 ^ Module.finrank (ZMod 2) (Additive Q) := hcard.symm.trans hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh).symm
  exact code_obstruction_of_normalized_cubic I U ρ D e xD zK tK hxD ht htD hDz hz3 hinv
    (fun v hv => hzfree v.toMul hv) (fun v hv => hxfree v.toMul hv) hdim

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
