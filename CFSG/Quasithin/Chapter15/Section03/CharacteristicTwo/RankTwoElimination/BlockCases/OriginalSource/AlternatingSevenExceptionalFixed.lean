module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenExceptionalRaw
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SplitMovedFixed
public import Theory.Representation.BinaryFourRankTwoFixed
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# The ordinary core in the exceptional A₇ second choice

For an injective core-to-star map, the actual Y₊ image retains three-rank two.
Such a group fixes no nonzero vector in a faithful binary four-space: a point
stabilizer in GL₄(2) has three-rank at most one. The split moved section then
turns Y₊-fixed seed vectors into L-fixed vectors, contradicting the original
normalizer bound for the selected plane. No assertion about the surviving
two-core of Y₊ is made.

Source: Aschbacher–Smith15.3.21, printed p.1127.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem raw_split_four_second_choice_false
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G)) (hYL : d.Yplus ≤ c.L)
    (hrank : primeRank 3 d.Yplus = 2)
    (hinj : Function.Injective (coreToStar hR))
    (hVW : d.V ≤ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype)
    (hN1 : normalizer (d.V₁ : Set G) ≤ d.M)
    (hYC : d.Yplus ≤ centralizer (d.V₁ : Set G)) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      IsCompl s.space.toSubmodule
        (fixedSpace ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)) →
      Function.Injective s.action →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 → False := by
  intro C J hCJ s hc hfaith hd
  let N := c.L ⊔ d.R
  let U := starV c.L d.R
  let ρ := (starRepresentation c.L d.R).comp J.subtype
  let f : c.L →* J := (C.subgroupOf J).subtype.comp
    ((subgroupOfEquivOfLe hCJ).symm.toMonoidHom.comp (toStarImage c.L d.R))
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* pCore 2 c.L := f.ker.subtype.codRestrict _ (by
      intro l
      apply (QuotientGroup.eq_one_iff _).mp
      apply hinj
      change coreToStar hR (QuotientGroup.mk' (pCore 2 c.L) (l : c.L)) = coreToStar hR 1
      rw [coreToStar_mk,map_one]
      have hh := congrArg (fun x : J => (x : StarQuotient c.L d.R))
        (show f l.val = 1 from l.property)
      apply Subtype.ext
      exact hh)
    exact pCore_isPGroup.of_injective j (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun t : pCore 2 c.L => (t : c.L)) hxy)
  let H := (d.Yplus.subgroupOf c.L).map f
  have hrH : primeRank 3 H = 2 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) f hk,
      primeRank_congr 3 (subgroupOfEquivOfLe hYL),hrank]
  have hHC : H ≤ C.subgroupOf J := by
    rintro _ ⟨y,hy,rfl⟩
    exact ((subgroupOfEquivOfLe hCJ).symm (toStarImage c.L d.R y)).property
  have hfix (w : Additive U) (hw : ∀ y : d.Yplus.subgroupOf c.L, ρ (f y) w = w) :
      w ∈ fixedSpace ρ (C.subgroupOf J) := by
    apply s.fixed_mem_fixed_of_split hc hHC
      (fun v hv => Representation.binaryFour_rankTwo_fixed_eq_zero s.action hfaith hd H hrH v hv) w
    intro y
    obtain ⟨z,hz,hzy⟩ := y.property
    change f z = (y : J) at hzy
    rw [←hzy]
    exact hw ⟨z,hz⟩
  have hplane : d.V₁ ≤ centralizer (c.L : Set G) := by
    intro x hx
    have hxV := d.action.plane_le 1 hx
    have hxN : x ∈ N := (hVW.trans (map_subtype_le _)) hxV
    let xN : N := ⟨x,hxN⟩
    have hxU : xN ∈ U := by
      obtain ⟨y,hy,he⟩ := hVW hxV
      exact (show y = xN from Subtype.ext he) ▸ hy
    let w : Additive U := Additive.ofMul ⟨xN,hxU⟩
    have hw : w ∈ fixedSpace ρ (C.subgroupOf J) := by
      apply hfix
      intro y
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      have he := congrArg Subtype.val (starRepresentation_apply c.L d.R
        (⟨y,mem_sup_left y.val.property⟩ : N) w)
      change (((starRepresentation c.L d.R
        (QuotientGroup.mk' (starKernel c.L d.R) (⟨y,mem_sup_left y.val.property⟩ : N)) w).toMul : N) : G) = x
      rw [he]
      change (y : G) * x * (y : G)⁻¹ = x
      have hm := (hYC y.property x hx).symm
      change (y : G) * x = x * (y : G) at hm
      rw [hm,mul_inv_cancel_right]
    intro l hl
    let lL : c.L := ⟨l,hl⟩
    have hh := hw ((subgroupOfEquivOfLe hCJ).symm (toStarImage c.L d.R lL))
    have he := congrArg (fun v : Additive U => ((v.toMul : N) : G)) hh
    have ha := congrArg Subtype.val (starRepresentation_apply c.L d.R
      (⟨l,mem_sup_left hl⟩ : N) w)
    change (((starRepresentation c.L d.R
      (QuotientGroup.mk' (starKernel c.L d.R) (⟨l,mem_sup_left hl⟩ : N)) w).toMul : N) : G) = x at he
    rw [ha] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  exact c.outside (((le_centralizer_iff.mp hplane).trans
    (Subgroup.centralizer_le_normalizer _)).trans hN1)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
