module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeStarGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenExceptionalRaw

/-!
# Normality of the actual A₇ star component

The original nonnormal-component catalogue leaves binary PSL₂ or PSL₃(2).
The first cannot cover A₇ because A₇ has an element of order four while every
binary SL₂ two-subgroup has exponent two. The second has order168 and cannot
surject onto A₇. Thus the component is normal in the actual selected local group.

Source: Aschbacher–Smith 1.2.1(3),15.3.11 and15.3.21, pp.503,1124,1127.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem not_injective_seven_to_binaryTwo
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (f : alternatingGroup (Fin 7) →* SL(2,E)) : ¬ Function.Injective f := by
  intro hf
  let x : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5,
      by
        change Equiv.Perm.sign _ = 1
        decide +kernel⟩
  have hx4 : x ^ 4 = 1 := by decide +kernel
  have hx2 : x ^ 2 ≠ 1 := by decide +kernel
  have hP : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx4)
  let P := (zpowers x).map f
  have he : (⟨f x,mem_map_of_mem f (mem_zpowers x)⟩ : P) ^ 2 = 1 :=
    Matrix.SpecialLinearGroup.twoSubgroup_pow_two P (hP.map f) _
  apply hx2
  apply hf
  have hh : f x ^ 2 = 1 := congrArg P.subtype he
  simpa only [map_pow,map_one] using hh

theorem alternatingSeven_star_component_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 7)) :
    (c.L.subgroupOf I).Normal := by
  by_contra hnormal
  let q := e.toMonoidHom.comp (coreToStar hR)
  have hq : Function.Surjective q := e.surjective.comp (coreToStar_surjective hR)
  rcases SourceRankOne.OriginalSource.source_component_models_of_nonnormal
    hG d hI hf c hnormal hS with ⟨m,hm,ha,_⟩ | ⟨ha,_⟩
  · obtain ⟨E,hfieldE,hfiniteE,hE,⟨a⟩⟩ := ha
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by simpa only [Nat.card_eq_fintype_card] using hE)
    have h4 : 3 < Nat.card E := by
      rw [hE]
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hm
      omega
    let : IsSimpleGroup PSL(2,E) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    let f := q.comp a.symm.toMonoidHom
    have hs : Function.Surjective f := hq.comp a.symm.surjective
    have hi : Function.Injective f := f.injective_of_surjective_of_simple hs
    let b := (MulEquiv.ofBijective f ⟨hi,hs⟩).symm.trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm
    exact not_injective_seven_to_binaryTwo b.toMonoidHom b.injective
  · obtain ⟨E,hfieldE,hfiniteE,hE,⟨a⟩⟩ := ha
    have hcE : Nat.card PSL(3,E) = 168 := by
      simpa [hE] using Matrix.PSL3.LinearThree.card_projective_mul_scalar E
    have hc : Nat.card (c.L ⧸ pCore 2 c.L) = 168 := (Nat.card_congr a.toEquiv).trans hcE
    have hd : Nat.card (alternatingGroup (Fin 7)) ∣ 168 := hc ▸ Subgroup.card_dvd_of_surjective q hq
    have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hcard] at hd
    exact (by decide : ¬2520 ∣ 168) hd
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
