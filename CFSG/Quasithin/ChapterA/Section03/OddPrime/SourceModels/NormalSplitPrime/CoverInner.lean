module
public import Theory.GroupTheory.CComponent.HexacodeTheta.InnerAction
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PrimeRankInvolutionLift

/-!
# The order-nine implementer of an inner outside cubic

For a normal component with center of order three, an inner automorphism
induced by an outside cubic has an implementer whose cube is central.
If that cube were trivial, removing the implementer would give an outside
centralizing cubic and enlarge an elementary nine to an elementary 27.
Thus the implementer has order nine and nonidentity central cube. Its
centralizer also has three-rank at most one, since the original outside
cubic fixes that whole centralizer.

The next module constructs a fixed elementary nine for linear covers,
and CoverSieve applies the contradiction on the literal two-core image.
Source: Aschbacher–Smith A.3.18, printed p.52.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverInner

private theorem fixed_rank_lt_two {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (x : G) (hx : orderOf x = 3) (hxK : x ∉ K)
    (hr : primeRank 3 G ≤ 2) (C : Subgroup K)
    (hC : ∀ c : C, Commute (c.val : G) x) : primeRank 3 C < 2 := by
  by_contra hn
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 3)
  let := hE
  obtain ⟨B,hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 2)
    (by rw [hcard]; exact pow_dvd_pow 3 (by omega))
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.of_injective B.subtype B.subtype_injective
  let f : E →* G := K.subtype.comp (C.subtype.comp E.subtype)
  have hf : Function.Injective f := K.subtype_injective.comp
    (C.subtype_injective.comp E.subtype_injective)
  let D := B.map f
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.map f
  have hdK : D ≤ K := by rintro _ ⟨b,_,rfl⟩; exact b.val.val.property
  have hfix : D ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨b,_,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hC b.val)
  have hc : Nat.card D = 3^2 := by rw [card_map_of_injective hf,hB]
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join D x hx
    (fun h => hxK (hdK h)) hfix hc
  omega

/-- An inner outside cubic forces an actual order-nine implementer whose
cube is a nonidentity element of the original component center. -/
theorem exists_nine_implementer {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hz : Nat.card (center K) = 3)
    (hrK : 1 < primeRank 3 K) (hr : primeRank 3 G ≤ 2)
    (x : G) (hx : orderOf x = 3) (hxK : x ∉ K)
    (hi : (MulAut.conjNormal x : MulAut K) ∈ MulAut.innerSubgroup K) :
    ∃ y : K, MulAut.conj y = MulAut.conjNormal x ∧ orderOf y = 9 ∧
      y ^ 3 ∈ center K ∧ y ^ 3 ≠ 1 ∧
      primeRank 3 (centralizer ({y} : Set K)) < 2 := by
  obtain ⟨y,hy⟩ := hi
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hyc : y ^ 3 ∈ center K := by
    have he : MulAut.conj (y ^ 3) = 1 := by
      rw [map_pow,hy,←map_pow,hx3,map_one]
    apply mem_center_iff.mpr
    intro z
    have hh := MulEquiv.congr_fun he z
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hy9 : y ^ 9 = 1 := by
    have hh : (⟨y^3,hyc⟩ : center K) ^ Nat.card (center K) = 1 := pow_card_eq_one'
    rw [hz] at hh
    have hh' : (y^3)^3=1 := congrArg Subtype.val hh
    simpa only [←pow_mul] using hh'
  have hy3 : y ^ 3 ≠ 1 := by
    intro h3
    let c : G := x * (y : G)⁻¹
    have hc : c ∈ centralizer (K : Set G) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer K]
      change MulAut.conjNormal (x * (y : G)⁻¹) = 1
      rw [map_mul,map_inv,MulAut.conjNormal_val,hy,mul_inv_cancel]
    have hcy : Commute c (y : G) := (mem_centralizer_iff.mp hc y y.property).symm
    have he : c * (y : G) = x := by simp [c,mul_assoc]
    have hc3 : c ^ 3 = 1 := by
      have hh := hcy.mul_pow 3
      rw [he,hx3,show (y : G)^3=1 from congrArg Subtype.val h3,mul_one] at hh
      exact hh.symm
    have hcK : c ∉ K := fun hh => hxK (he ▸ K.mul_mem hh y.property)
    have hco : orderOf c = 3 := orderOf_eq_prime hc3 (fun hh => hcK (hh ▸ K.one_mem))
    have hh := fixed_rank_lt_two K c hco hcK hr (⊤ : Subgroup K) (fun k =>
      mem_centralizer_iff.mp hc k.val k.val.property)
    rw [primeRank_congr 3 topEquiv] at hh
    omega
  refine ⟨y,hy,?_,hyc,hy3,?_⟩
  · exact orderOf_eq_prime_pow (p := 3) (n := 1) hy3 hy9
  · apply fixed_rank_lt_two K x hx hxK hr
    intro c
    have hh := MulEquiv.congr_fun hy c.val
    have hcomm := mem_centralizer_singleton_iff.mp c.property
    have he : (MulAut.conjNormal x : MulAut K) c.val = c.val := by
      rw [←hh]
      exact (mul_inv_eq_iff_eq_mul).mpr hcomm.symm
    have he' := congrArg Subtype.val he
    exact ((mul_inv_eq_iff_eq_mul).mp he').symm

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverInner
