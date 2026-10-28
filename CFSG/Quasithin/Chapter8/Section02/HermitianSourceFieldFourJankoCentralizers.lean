module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualAbelianBound
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.ResidualElementary
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
import all Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.NormalElementary
import all Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.ResidualElementary

/-!
# Nine-spaces and the actual J₄ involution-centralizer residuals

The first centralizer bounds every residual-normalized abelian two-subgroup
by 256. In the second, a residual-normalized nine-space lies in the full
order-2048 two-core. An element of order eleven in the residual fixes that
nine-space by orbit counting, and consequently fixes the entire two-core.
This contradicts the native two-core centralizer calculation.

The obstruction descends through arbitrary odd kernels and central
two-kernels, retaining the literal element-centralizer map. In the latter
case its image need not be the whole centralizer: its two-group cokernel
still lets the full perfect residual lift. The Chapter 12 consumer applies
this to the unchanged Hermitian nine-space in both original J₄ branches.
Source: Aschbacher--Smith 4.4.3, printed pp.622--623, as used in 8.2.7,
printed p.718, refs/quasithin.pdf; GLS3 Table 5.3i. Imported native matrix
certificates retain their source attribution. Proof-only imports reuse the
local orbit-counting and two-core placement lemmas without changing APIs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Janko4.InvolutionCentralizers
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem second_no_nine_residual
    (W : Subgroup Second.ambientCentralizer) [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 512)
    (hn : solvableResidual Second.ambientCentralizer ≤ normalizer (W : Set _)) : False := by
  let C := Second.ambientCentralizer
  let R := solvableResidual C
  have hQ : IsPGroup 2 (C ⧸ R) := by
    have he := Janko4.LocalStructure.involution_centralizer_residuals
      (Second.seed : Janko4.Model) Second.seed_order
    change pResidual 2 C = R at he
    exact (isPGroup_quotient_pResidual (G := C) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq he)
  have hWK : W ≤ Second.ambientKernel := by
    rw [←Second.ambient_twoCore_eq_kernel]
    exact normalized_by_residual_le_core W (IsElementaryAbelian.isPGroup 2 W) hn hQ
  have hWR : W ≤ R := hWK.trans Second.kernel_le_residual
  let U := W.subgroupOf R
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer hWR).mpr hn
  have hU : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 W).comap_subtype
  have hUc : Nat.card U = 512 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWR).toEquiv).trans hcard
  have hd : 11 ∣ Nat.card C := by rw [Second.ambient_card]; decide
  have hcop : Nat.Coprime 11 R.index := by
    obtain ⟨k,hk⟩ := hQ.exists_card_eq
    change Nat.Coprime 11 (Nat.card (C ⧸ R))
    rw [hk]
    exact (by decide : Nat.Coprime 11 2).pow_right k
  have hdR : 11 ∣ Nat.card R := hcop.dvd_of_dvd_mul_right (R.card_mul_index.symm ▸ hd)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 11 hdR
  obtain ⟨k,hk,hle,hmod⟩ := eleven_fixed_card U hU x hx
  rw [hUc] at hle hmod
  have hk9 : k ≤ 9 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at hh'
    omega
  have he : 2^k = 512 := by
    interval_cases k <;> norm_num at hmod
    rfl
  have hfix : U ≤ centralizer (zpowers x : Set R) := by
    have heq : U ⊓ centralizer (zpowers x : Set R) = U :=
      eq_of_le_of_card_ge inf_le_left (by rw [hk,he,hUc])
    exact heq.ge.trans inf_le_right
  have hWC : W ≤ centralizer (zpowers (x : C) : Set C) := by
    intro w hw
    rw [zpowers_eq_closure,centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr
      (congrArg R.subtype (hfix (show (⟨w,hWR hw⟩ : R) ∈ U from hw) x (mem_zpowers x))).symm
  let := Second.ambientKernel_elementary
  have hx' : orderOf (x : C) = 11 := (orderOf_coe x).trans hx
  obtain ⟨j,hj,hlej,hmodj⟩ := eleven_fixed_card Second.ambientKernel
    (IsElementaryAbelian.isPGroup 2 _) x hx'
  rw [Second.ambientKernel_card] at hlej hmodj
  have hj11 : j ≤ 11 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at hh'
    omega
  have hlo : 512 ≤ 2^j := by
    have hh := card_le_of_le (le_inf hWK hWC)
    rwa [hcard,hj] at hh
  have hej : 2^j = 2048 := by
    interval_cases j <;> norm_num at hmodj <;> norm_num at hlo
    rfl
  have hKC : Second.ambientKernel ≤ centralizer (zpowers (x : C) : Set C) := by
    have heq : Second.ambientKernel ⊓ centralizer (zpowers (x : C) : Set C) =
        Second.ambientKernel := eq_of_le_of_card_ge inf_le_left
          (by rw [hj,hej,Second.ambientKernel_card])
    exact heq.ge.trans inf_le_right
  have hxK : (x : C) ∈ Second.ambientKernel := by
    rw [←Second.ambientKernel_selfCentralizing]
    exact le_centralizer_iff.mp hKC (mem_zpowers (x : C))
  have hbad : 11 ∣ 2048 := by
    rw [←Second.ambientKernel_card,←hx',orderOf_coe (⟨x,hxK⟩ : Second.ambientKernel)]
    exact orderOf_dvd_natCard _
  norm_num at hbad

/-- Neither native J₄ involution centralizer has a residual-invariant nine-space. -/
theorem janko_no_nine_residual
    (z : Janko4.Model) (hz : orderOf z = 2)
    (W : Subgroup (centralizer ({z} : Set Janko4.Model))) [IsElementaryAbelian 2 W]
    (hc : Nat.card W = 512)
    (hn : solvableResidual (centralizer ({z} : Set Janko4.Model)) ≤ normalizer (W : Set _)) :
    False := by
  rcases centralizer_equiv_first_or_second z hz with hfirst | hsecond
  · obtain ⟨e⟩ := hfirst
    let E := W.map e.toMonoidHom
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
    have hne : solvableResidual First.centralizer ≤ normalizer (E : Set _) := by
      rw [←map_solvableResidual_eq e.toMonoidHom e.surjective]
      exact (map_mono hn).trans (W.le_normalizer_map e.toMonoidHom)
    have hh := First.residual_normalized_abelian_card_le E (IsElementaryAbelian.isPGroup 2 E) hne
    rw [card_map_of_injective e.injective,hc] at hh
    omega
  · obtain ⟨e⟩ := hsecond
    let E := W.map e.toMonoidHom
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
    apply second_no_nine_residual E (by rwa [card_map_of_injective e.injective])
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact (map_mono hn).trans (W.le_normalizer_map e.toMonoidHom)

private theorem residual_map_of_residual_le_range
    {C D : Type*} [Group C] [Finite C] [Group D] [Finite D]
    (f : C →* D) (hr : solvableResidual D ≤ f.range) :
    (solvableResidual C).map f = solvableResidual D := by
  calc
    (solvableResidual C).map f =
        ((solvableResidual C).map f.rangeRestrict).map f.range.subtype := by
      rw [map_map]; rfl
    _ = (solvableResidual f.range).map f.range.subtype := by
      rw [map_solvableResidual_eq f.rangeRestrict f.rangeRestrict_surjective]
    _ = _ := map_solvableResidual_eq_of_residual_le f.range hr

private theorem no_nine_residual_image
    {C : Type*} [Group C] [Finite C]
    (z : Janko4.Model) (hz : orderOf z = 2)
    (f : C →* centralizer ({z} : Set Janko4.Model))
    (hr : solvableResidual (centralizer ({z} : Set Janko4.Model)) ≤ f.range)
    (W : Subgroup C) [IsElementaryAbelian 2 W]
    (hi : Function.Injective (f.comp W.subtype)) (hc : Nat.card W = 512)
    (hn : solvableResidual C ≤ normalizer (W : Set C)) : False := by
  let U := W.map f
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map f
  have hcard : Nat.card U = Nat.card W := by
    have he := MonoidHom.ofInjective hi
    have hh : (f.comp W.subtype).range = U := by rw [MonoidHom.range_comp,range_subtype]
    exact (Nat.card_congr (he.trans (MulEquiv.subgroupCongr hh)).toEquiv).symm
  apply janko_no_nine_residual z hz U (hcard.trans hc)
  rw [←residual_map_of_residual_le_range f hr]
  exact (map_mono hn).trans (W.le_normalizer_map f)

/-- The native obstruction retains any odd kernel of the component projection. -/
theorem janko_no_nine_residual_odd_cover
    {K : Type*} [Group K] [Finite K]
    (f : K →* Janko4.Model) (hf : Function.Surjective f)
    (hk : Nat.Coprime 2 (Nat.card f.ker))
    (z : K) (hz : orderOf z = 2)
    (W : Subgroup (centralizer ({z} : Set K))) [IsElementaryAbelian 2 W]
    (hc : Nat.card W = 512)
    (hn : solvableResidual (centralizer ({z} : Set K)) ≤ normalizer (W : Set _)) : False := by
  let c := f.elementCentralizerMap z
  have hs : Function.Surjective c := f.elementCentralizerMap_surjective_of_odd_kernel hf hk z hz
  have hi : Function.Injective (c.comp W.subtype) := by
    have hk' : Nat.Coprime 2 (Nat.card c.ker) := by
      rw [f.elementCentralizerMap_ker z]
      exact hk.of_dvd_right (card_dvd_of_injective
        ((centralizer ({z} : Set K)).subtype.subgroupComap f.ker)
        (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun w : f.ker => (w : K)) h))))
    exact injective_comp_subtype_of_coprime_ker c hk' W (IsElementaryAbelian.isPGroup 2 W)
  exact no_nine_residual_image (f z) (orderOf_map_involution_of_odd_kernel f hk hz)
    c (by rw [MonoidHom.range_eq_top.mpr hs]; exact le_top) W hi hc hn

/-- Central two-kernels are retained; only the original nine-space must embed. -/
theorem janko_no_nine_residual_two_cover
    {K : Type*} [Group K] [Finite K]
    (f : K →* Janko4.Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center K) (hp : IsPGroup 2 f.ker)
    (z : K) (hz : orderOf (f z) = 2)
    (W : Subgroup (centralizer ({z} : Set K))) [IsElementaryAbelian 2 W]
    (hi : Function.Injective ((f.elementCentralizerMap z).comp W.subtype))
    (hc : Nat.card W = 512)
    (hn : solvableResidual (centralizer ({z} : Set K)) ≤ normalizer (W : Set _)) : False := by
  obtain ⟨hnr,hq⟩ := f.elementCentralizerMap_normal_pGroup_cokernel hf hk hp z
  let := hnr
  let := hq.isNilpotent
  exact no_nine_residual_image (f z) hz (f.elementCentralizerMap z)
    (solvableResidual_le_of_solvable_quotient _) W hi hc hn

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
