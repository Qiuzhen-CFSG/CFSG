module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Normalization
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.LinearQuotient
public import Theory.GroupTheory.NormalSylowCoreCentralizer
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# The exact kernel of the cover action

Write M = N_T(E)Y and D = O²(C_L(r)). The local centralizer of L at z is
⟨z⟩, by its central Sylow subgroup and E1. The intrinsic residual-fixer
bound and the irreducible C_Q(E)-action therefore put C_M(E) ∩ C_M(D) in E.
The kernel of M's action on D has order dividing 24. A three-element in
that kernel would centralize an independent E₉ in the two-local N_G(E),
contrary to quasithinness. The kernel is consequently a two-group. Its
normality and the transitive Y-action on E's three nonidentity elements
force it to fix E pointwise, proving that the full kernel is exactly E.

All normality assertions are relative to the indicated local overgroup.
The supplied model placement, normalization and transitivity are proved
by the final assembly using Cover.Normalization and Cover.Frattini.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.4(2) and the proof of 16.4.9(2), printed pp.1184 and 1191.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The order-two instance of source 16.4.4(2). The normal local centralizer
has central Sylow subgroup ⟨z⟩ and trivial odd core, hence equals ⟨z⟩. -/
theorem component_centralizer_at_z
    (h : IntersectionSetup T z L g R) (hE : HasEvenTypeCentralizers G)
    (hTC : commutingSylow T L = zpowers z) :
    centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = zpowers z := by
  let C := centralizer ({z} : Set G)
  let B := (centralizer (L : Set G)).subgroupOf C
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    ((Centerless.centralizer_z_le_normalizer h).trans
      (normalizer_le_normalizer_centralizer L))
  let S := T.subtype h.sylow_centralizes
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal B
  have huT {u : B} (hu : u ∈ (U : Subgroup B)) : ((u : C) : G) ∈ (T : Subgroup G) := by
    rw [hU] at hu
    exact hu
  have huZ {u : B} (hu : u ∈ (U : Subgroup B)) : ((u : C) : G) ∈ zpowers z :=
    hTC ▸ (show ((u : C) : G) ∈ commutingSylow T L from ⟨huT hu, u.property⟩)
  have hcentral : (U : Subgroup B) ≤ center B := by
    intro u hu
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    apply Subtype.ext
    have hb : zpowers z ≤ centralizer ({((b : C) : G)} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (b : C).property).symm)
    exact (mem_centralizer_singleton_iff.mp (hb (huZ hu))).symm
  let : (U : Subgroup B).Normal := ⟨by
    intro u hu b
    rw [mem_center_iff.mp (hcentral hu) b, mul_inv_cancel_right]
    exact hu⟩
  have hodd : pPrimeCore 2 B = ⊥ := by
    have hm : (pPrimeCore 2 B).map B.subtype = ⊥ :=
      pPrimeCore_eq_bot_iff.mp (hE.oddCore z h.involution) _ inferInstance
        (Nat.Coprime.of_dvd_right (card_map_dvd _ B.subtype) pPrimeCore_coprime_card)
    exact map_injective (f := B.subtype) Subtype.val_injective
      (by simpa only [Subgroup.map_bot] using hm)
  have hbound := U.centralizer_le_sup_pPrimeCore_of_normal
  rw [hodd, sup_bot_eq] at hbound
  apply le_antisymm
  · intro x hx
    let b : B := ⟨⟨x, hx.2⟩, hx.1⟩
    apply huZ (u := b)
    apply hbound
    intro u hu
    exact (mem_center_iff.mp (hcentral hu) b).symm
  · rw [← hTC]
    exact le_inf inf_le_right (inf_le_left.trans h.sylow_centralizes)


omit [Finite G] in
/-- The actual cover overgroup preserves the chosen Sylow centralizer. -/
theorem coverOvergroup_le_coverNormalizer :
    coverOvergroup T r z ≤ coverNormalizer T r z := by
  apply sup_le ?_ (map_subtype_le _)
  intro x hx
  refine ⟨hx.2, ?_⟩
  change x ∈ normalizer (((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G)) : Set G)
  apply (mem_normalizer_iff_map_conj_eq (H := (T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))).mpr
  change ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G)).map
    (MulAut.conj x).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj x).injective]
  change (T : Subgroup G).conjBy x ⊓
    (centralizer (fourGroup r z : Set G)).conjBy x = _
  have hT : (T : Subgroup G).conjBy x = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer hx.1)
  have hC : (centralizer (fourGroup r z : Set G)).conjBy x =
      centralizer (fourGroup r z : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_centralizer _ hx.2)
  rw [hT, hC]

private theorem residual_fixer_four_le
    (h : IntersectionSetup T z L g R)
    (hKC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = zpowers z)
    (hr : r ∈ R)
    (d : NormalizerData L r z) :
    centralizer (fourGroup r z : Set G) ⊓ centralizer (residual L r : Set G) ≤
      residual L r ⊔ fourGroup r z := by
  let K := centralizer (L : Set G)
  let B := residual L r ⊔ zpowers r
  have hBN : B ≤ normalizer (K : Set G) := by
    rw [h.normalizers_eq]
    exact sup_le ((residual_le_centralizer L r).trans (inf_le_left.trans L.le_normalizer))
      (zpowers_le.mpr (h.sylow_normalizes (h.le_sylow hr)))
  have hBC : B ≤ centralizer ({z} : Set G) :=
    sup_le ((residual_le_centralizer L r).trans (inf_le_left.trans h.component.1))
      (zpowers_le.mpr (h.sylow_centralizes (h.le_sylow hr)))
  intro x hx
  have hxz : x ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hx.1 z (mem_sup_right (mem_zpowers z))).symm
  have hprod : x ∈ K ⊔ B := by
    rw [← sup_assoc]
    exact d.residual_fixer ⟨Centerless.centralizer_z_le_normalizer h hxz, hx.2⟩
  change x ∈ ((K ⊔ B : Subgroup G) : Set G) at hprod
  rw [coe_mul_of_right_le_normalizer_left K B hBN] at hprod
  obtain ⟨k, hk, b, hb, rfl⟩ := hprod
  have hkz : k ∈ centralizer ({z} : Set G) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer ({z} : Set G)).mul_mem hxz
        ((centralizer ({z} : Set G)).inv_mem (hBC hb))
  have hkE : k ∈ fourGroup r z := mem_sup_right (hKC ▸ (show k ∈ K ⊓ involutionCentralizer z from ⟨hk, hkz⟩))
  have hbDE : b ∈ residual L r ⊔ fourGroup r z :=
    (show B ≤ residual L r ⊔ fourGroup r z from
      sup_le le_sup_left (le_sup_left.trans le_sup_right)) hb
  exact (residual L r ⊔ fourGroup r z).mul_mem (mem_sup_right hkE) hbDE

private theorem cover_fixer_four_le
    (h : IntersectionSetup T z L g R)
    (hKC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = zpowers z)
    (hr : r ∈ R)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hQT : d.Q ≤ (T : Subgroup G)) :
    coverOvergroup T r z ⊓ centralizer (fourGroup r z : Set G) ⊓
      centralizer (residual L r : Set G) ≤ fourGroup r z := by
  have hdis := residual_disjoint_coverNormalizer d c hD h9 (inf_le_left.trans hQT)
  have hEM : fourGroup r z ≤ coverOvergroup T r z :=
    (le_inf (fourGroup_le_sylow h hr) (fourGroup r z).le_normalizer).trans le_sup_left
  have hEN : fourGroup r z ≤ normalizer (residual L r : Set G) :=
    (le_centralizer_iff.mp (residual_le_fourGroup_centralizer h)).trans (centralizer_le_normalizer _)
  intro x hx
  have hprod := residual_fixer_four_le h hKC hr d ⟨hx.1.2, hx.2⟩
  change x ∈ ((residual L r ⊔ fourGroup r z : Subgroup G) : Set G) at hprod
  rw [coe_mul_of_right_le_normalizer_left _ _ hEN] at hprod
  obtain ⟨a, ha, e, he, rfl⟩ := hprod
  have haM : a ∈ coverOvergroup T r z := by
    simpa only [mul_inv_cancel_right] using
      (coverOvergroup T r z).mul_mem hx.1.1 ((coverOvergroup T r z).inv_mem (hEM he))
  have ha1 := disjoint_def.mp hdis ha (coverOvergroup_le_coverNormalizer haM)
  change a * e ∈ fourGroup r z
  rw [ha1, one_mul]
  exact he

/-- The action of the actual N_T(E)Y on D has precisely E as its kernel.
Quasithinness excludes a three-element in the kernel; transitivity excludes
a nontrivial normal two-group action on E. -/
theorem coverResidualAction_kernel_exact
    (h : IntersectionSetup T z L g R)
    (hE : HasEvenTypeCentralizers G)
    (hqt : IsQuasithin G)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hQT : d.Q ≤ (T : Subgroup G))
    (hDN : coverOvergroup T r z ≤ normalizer (residual L r : Set G))
    (htrans : CoverTransitive T r z) :
    (coverResidualAction T r z (residual L r) hDN).ker =
      (fourGroup r z).subgroupOf (coverOvergroup T r z) := by
  have hKC := component_centralizer_at_z h hE hTC
  let M := coverOvergroup T r z
  let E := fourGroup r z
  let a := coverResidualAction T r z (residual L r) hDN
  let K := a.ker
  let f : M →* MulAut E := E.normalizerMonoidHom.comp
    (inclusion (coverOvergroup_le_normalizer T r z))
  let fK := f.comp K.subtype
  have hfour := fourGroup_elementary_card h hr hr2 hout
  let : IsElementaryAbelian 2 E := hfour.1
  let : Nontrivial E := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hfour.2]; decide)
  let : IsKleinFour E := ⟨hfour.2, IsElementaryAbelian.exponent_eq_prime⟩
  have hfixD (x : K) : ((x : M) : G) ∈ centralizer (residual L r : Set G) := by
    have hx := x.property
    change (x : M) ∈ a.ker at hx
    rw [coverResidualAction_kernel] at hx
    exact hx
  have hkerE (x : fK.ker) : (((x : K) : M) : G) ∈ E := by
    apply cover_fixer_four_le h hKC hr d c hD h9 hQT
    refine ⟨⟨(x : K).val.property, ?_⟩, hfixD x⟩
    intro e he
    have hh := congrArg (fun b : MulAut E => b ⟨e, he⟩) x.property
    have heq : (((x : K) : M) : G) * e * (((x : K) : M) : G)⁻¹ = e :=
      congrArg Subtype.val hh
    exact ((mul_inv_eq_iff_eq_mul).mp heq).symm
  let j : fK.ker →* E :=
    { toFun := fun x => ⟨(((x : K) : M) : G), hkerE x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    have heG : (((x : K) : M) : G) = (((y : K) : M) : G) :=
      congrArg (fun v : E => (v : G)) he
    exact Subtype.ext (Subtype.ext (Subtype.ext heG))
  have hk4 : Nat.card fK.ker ∣ 4 := hfour.2 ▸ card_dvd_of_injective j hj
  have hr6 : Nat.card fK.range ∣ 6 :=
    IsKleinFour.card_mulAut E ▸ fK.range.card_subgroup_dvd_card
  have hk24 : Nat.card K ∣ 24 := by
    have hh := Nat.mul_dvd_mul hk4 hr6
    rw [← index_ker fK, fK.ker.card_mul_index] at hh
    exact hh
  have hn3 : ¬ 3 ∣ Nat.card K := by
    intro hd
    obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hd
    have hxN : (((x : M) : G)) ∈ normalizer (E : Set G) :=
      coverOvergroup_le_normalizer T r z x.val.property
    have hxG3 : orderOf (((x : M) : G)) = 3 :=
      (orderOf_coe x.val).trans ((orderOf_coe x).trans hx3)
    have hxD : (((x : M) : G)) ∉ residual L r := by
      intro hx
      have he := disjoint_def.mp
        (residual_disjoint_coverNormalizer d c hD h9 (inf_le_left.trans hQT)) hx
        (coverOvergroup_le_coverNormalizer x.val.property)
      simp [he] at hxG3
    exact no_independent_centralizing_three h hqt hr hr2 hout hD h9 hxN hxG3 hxD
      (fun v hv => mem_centralizer_singleton_iff.mpr (hfixD x v hv))
  have hK2 : IsPGroup 2 K := by
    apply IsPGroup.of_card_dvd_pow (n := 3)
    have hcop : Nat.Coprime (Nat.card K) 3 :=
      (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hn3 |>.symm
    exact hcop.dvd_of_dvd_mul_right (show Nat.card K ∣ 2 ^ 3 * 3 from hk24)
  let : MulDistribMulAction M E := MulDistribMulAction.compHom E f
  obtain ⟨w, hw, hw1⟩ := hK2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := E) (by rw [hfour.2]; decide : 2 ∣ Nat.card E)
    (show (1 : E) ∈ MulAction.fixedPoints K E by simp [MulAction.mem_fixedPoints])
  have hwG : (w : G) ≠ 1 := fun he => hw1 (Subtype.ext he).symm
  have hall (u : E) : u ∈ MulAction.fixedPoints K E := by
    by_cases hu : u = 1
    · subst u; simp [MulAction.mem_fixedPoints]
    have huG : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
    obtain ⟨y, hy, hyw⟩ := htrans w w.property hwG u u.property huG
    let yM : M := ⟨y, mem_sup_right hy⟩
    have he : yM • w = u := Subtype.ext hyw
    exact he ▸ smul_mem_fixedPoints_of_normal yM hw
  apply le_antisymm ?_ (residual_fourGroup_subgroupOf_le_coverResidualAction_kernel h hr hDN)
  intro x hx
  apply cover_fixer_four_le h hKC hr d c hD h9 hQT
  refine ⟨⟨x.property, ?_⟩, hfixD ⟨x, hx⟩⟩
  intro e he
  have hh := hall ⟨e, he⟩ ⟨x, hx⟩
  have heq : (x : G) * e * (x : G)⁻¹ = e := congrArg Subtype.val hh
  exact ((mul_inv_eq_iff_eq_mul).mp heq).symm


end CFSG.Quasithin.Chapter16.Intersections.GraphField
