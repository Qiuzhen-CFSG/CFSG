module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Escaping component in the outer A₆–C₃ alternative

In the literal extension of B.5.6(4), the product of the specified factors
is the two-residual: its quotient is cyclic and offender generation makes
that quotient a two-group, while A₆ and C₃ lie in the residual. The center
of this product is precisely the specified cubic factor. Consequently that
factor is characteristic in the actor and normal in every ambient group
in which the actor is normal.

A two-perfect subgroup Y centralizes this normal cubic factor, whose
automorphism group has order two. Thus the cubic factor lies in N(Y).
The residual together with the Sylow intersection generates the actor;
if the actor escapes M = N(Y), its A₆ factor must escape M as well.
The factor is an ordinary component by its actual subnormal embedding
and the simplicity and perfectness of A₆.

The extension, factor maps and conjugation actions are those supplied by
`OuterSixThreeCase`; no splitting is assumed. The selection requires
neither a two-core condition on the actor nor solvability of Y.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3 and
B.5.6(4), printed pp.104–105; the component selections in 15.3.15(2) and
15.3.26(2), printed pp.1123–1126 and 1130.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.OuterBranch
variable {D : Type*} [Group D]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) D V} (c : OuterSixThreeCase ρ)

private theorem first_perfect : Group.IsPerfect c.first := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := c.firstEquiv.symm.toMonoidHom) c.firstEquiv.symm.surjective

private theorem first_twoPerfect [Finite D] : IsPPerfect 2 c.first := by
  let := first_perfect c
  intro K hK hp
  let := hK
  have hs : Subsingleton (c.first ⧸ K) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (c.first ⧸ K) hp.isNilpotent
  exact QuotientGroup.subgroup_eq_top_of_subsingleton K hs

private theorem second_card : Nat.card c.second = 3 := by
  rw [Nat.card_congr c.secondEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The literal two factors form the two-residual, without assuming a split extension. -/
theorem residual_eq_product [Finite D] (hg : offenderSubgroup ρ = ⊤) :
    pResidual 2 D = c.first ⊔ c.second := by
  let := c.product_normal
  let := c.quotient_isCyclic
  let := IsCyclic.commGroup (α := D ⧸ (c.first ⊔ c.second))
  have hq := abelian_image_isTwoGroup ρ (QuotientGroup.mk' (c.first ⊔ c.second))
    (QuotientGroup.mk'_surjective _) hg
  refine le_antisymm (show pResidual 2 D ≤ c.first ⊔ c.second from
    sInf_le ⟨inferInstance, hq⟩) ?_
  apply sup_le (le_pResidual_of_isPPerfect _ (first_twoPerfect c))
  intro b hb
  apply mem_pResidual_of_orderOf_coprime
  exact (show Nat.Coprime 2 3 by decide).of_dvd_right
    (second_card c ▸ c.second.orderOf_dvd_natCard hb)

private theorem first_center : center c.first = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have he := (centerCongr c.firstEquiv ⟨a, ha⟩).property
  change c.firstEquiv a ∈ center (alternatingGroup (Fin 6)) at he
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  exact mem_bot.mpr (c.firstEquiv.map_eq_one_iff.mp he)

/-- The center of the literal product is its specified cyclic factor. -/
theorem product_center :
    (center (c.first ⊔ c.second : Subgroup D)).map (c.first ⊔ c.second).subtype =
      c.second := by
  have hcomm (a b : c.second) : a * b = b * a := by
    apply c.secondEquiv.injective
    simp only [map_mul, mul_comm]
  apply le_antisymm
  · rintro x ⟨z, hz, rfl⟩
    have hc := (centerCongr c.product.symm ⟨z, hz⟩).property
    change c.product.symm z ∈ center (c.first × c.second) at hc
    rw [Subgroup.center_prod] at hc
    have hfirst : (c.product.symm z).1 = 1 := by
      have hh : (c.product.symm z).1 ∈ center c.first := hc.1
      rw [first_center c, mem_bot] at hh
      exact hh
    have he := congrArg Subtype.val (c.product.apply_symm_apply z)
    rw [c.product_apply, hfirst, Subgroup.coe_one, one_mul] at he
    change (z : D) ∈ c.second
    exact he ▸ (c.product.symm z).2.property
  · intro b hb
    have hc : ((1 : c.first), (⟨b, hb⟩ : c.second)) ∈ center (c.first × c.second) := by
      rw [Subgroup.center_prod]
      exact ⟨one_mem _, mem_center_iff.mpr (fun a => hcomm a _)⟩
    refine ⟨c.product (1, ⟨b, hb⟩),
      (centerCongr c.product ⟨_, hc⟩).property, ?_⟩
    change (c.product (1, ⟨b, hb⟩) : D) = b
    simp only [c.product_apply, Subgroup.coe_one, one_mul]

/-- The cyclic factor is characteristic in the offender-generated actor. -/
theorem second_characteristic [Finite D] (hg : offenderSubgroup ρ = ⊤) :
    c.second.Characteristic := by
  let : (c.first ⊔ c.second).Characteristic := by
    rw [← residual_eq_product c hg]
    infer_instance
  rw [← product_center c]
  infer_instance

/-- The alternating factor is an ordinary component of the original actor. -/
theorem first_component : IsComponent D c.first := by
  let P := c.first ⊔ c.second
  let f : P →* c.second := (MonoidHom.snd c.first c.second).comp c.product.symm.toMonoidHom
  have hf : f.ker = c.first.subgroupOf P := by
    apply le_antisymm
    · intro x hx
      have hb : (c.product.symm x).2 = 1 := hx
      have he := congrArg Subtype.val (c.product.apply_symm_apply x)
      rw [c.product_apply, hb, Subgroup.coe_one, mul_one] at he
      change (x : D) ∈ c.first
      exact he ▸ (c.product.symm x).1.property
    · intro x hx
      have he : c.product (⟨x, hx⟩, 1) = x := by
        apply Subtype.ext
        simp only [c.product_apply, Subgroup.coe_one, mul_one]
      change (c.product.symm x).2 = 1
      rw [← he, c.product.symm_apply_apply]
  have hn : (c.first.subgroupOf P).Normal := hf ▸ inferInstance
  refine ⟨.step _ P le_sup_left c.product_normal.isSubnormal hn, ?_⟩
  let := first_perfect c
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup c.first := c.firstEquiv.isSimpleGroup
  refine { toIsPerfect := inferInstance, simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq (first_center c)).trans
    QuotientGroup.quotientBot).isSimpleGroup

variable {A : Type*} [Group A] [Finite A]

/-- The normal cubic factor belongs to the exact normalizer of every two-perfect Y. -/
theorem second_le_normalizer (N : Subgroup A) [N.Normal]
    {ρ : Representation (ZMod 2) N V} (c : OuterSixThreeCase ρ)
    (hg : offenderSubgroup ρ = ⊤) (Y : Subgroup A) (hY : IsPPerfect 2 Y) :
    c.second.map N.subtype ≤ normalizer (Y : Set A) := by
  let := second_characteristic c hg
  let R := c.second.map N.subtype
  have hR : Nat.card R = 3 := by
    rw [card_map_of_injective N.subtype_injective]
    exact second_card c
  let : IsCyclic R := isCyclic_of_prime_card hR
  have hp : IsPGroup 2 (MulAut R) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut, hR]; decide)
  let f : Y →* MulAut R := (MulAut.conjNormal : A →* MulAut R).comp Y.subtype
  have hf := hY.hom_eq_one_of_isPGroup hp f
  have hc : Y ≤ centralizer (R : Set A) := by
    intro y hy r hr
    have hh := congrArg (fun g : Y →* MulAut R => g ⟨y, hy⟩ ⟨r, hr⟩) hf
    have he : y * r * y⁻¹ = r := congrArg Subtype.val hh
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)

/-- The A₆ component must escape M in the outer A₆–C₃ alternative. -/
theorem first_outside (N Y M : Subgroup A) [N.Normal] (S : Sylow 2 A)
    (hY : IsPPerfect 2 Y) (hSM : (S : Subgroup A) ≤ M)
    (hM : normalizer (Y : Set A) = M) (hNM : ¬ N ≤ M)
    {ρ : Representation (ZMod 2) N V} (hg : offenderSubgroup ρ = ⊤)
    (c : OuterSixThreeCase ρ) : ¬ c.first.map N.subtype ≤ M := by
  intro hfirst
  have hsecond : c.second.map N.subtype ≤ M :=
    (second_le_normalizer N c hg Y hY).trans_eq hM
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal N
  have hgen := congrArg (fun E : Subgroup N => E.map N.subtype)
    (pResidual_sup_sylow_eq_top P)
  rw [residual_eq_product c hg, Subgroup.map_sup, Subgroup.map_sup,
    ← MonoidHom.range_eq_map, range_subtype, hP, subgroupOf_map_subtype] at hgen
  exact hNM (hgen ▸ sup_le (sup_le hfirst hsecond) (inf_le_left.trans hSM))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.OuterBranch

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection
variable {A : Type*} [Group A] [Finite A]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Select an escaping ordinary component in the complete outer source branch. -/
theorem exists_component_outside_of_outerSixThree
    (N Y M : Subgroup A) [N.Normal] (S : Sylow 2 A)
    (hY : IsPPerfect 2 Y) (hSM : (S : Subgroup A) ≤ M)
    (hM : normalizer (Y : Set A) = M) (hNM : ¬ N ≤ M)
    (ρ : Representation (ZMod 2) N V) (hg : offenderSubgroup ρ = ⊤)
    (c : OuterSixThreeCase ρ) :
    ∃ E : Subgroup N, IsComponent N E ∧ ¬ E.map N.subtype ≤ M :=
  ⟨c.first, OuterBranch.first_component c,
    OuterBranch.first_outside N Y M S hY hSM hM hNM hg c⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
open StarSelection.QuotientSelection
variable {G : Type*} [Group G] [Finite G] (d : LocalData G)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Apply the outer-branch selection to the literal Thompson star image. -/
theorem exists_star_component_of_outerSixThree {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hθ : theta (d.MI I) = d.Yplus)
    (hN : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M)
    (ρ : Representation (ZMod 2) (d.thompsonStar I) V)
    (hg : offenderSubgroup ρ = ⊤) (c : OuterSixThreeCase ρ) :
    ∃ E : Subgroup (d.thompsonStar I), IsComponent (d.thompsonStar I) E ∧
      ¬ E.map (d.thompsonStar I).subtype ≤ d.starImage I d.M := by
  obtain ⟨P, hP⟩ := d.exists_starSylow hS
  apply exists_component_outside_of_outerSixThree (d.thompsonStar I)
    (d.starImage I d.Yplus) (d.starImage I d.M) P
    (d.starYplus_twoPerfect hI hθ) ?_ hN hJ ρ hg c
  rw [hP]
  exact map_mono (comap_mono (inf_le_left.trans d.sylow_le))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
