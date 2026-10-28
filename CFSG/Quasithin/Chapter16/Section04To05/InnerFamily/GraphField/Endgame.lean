module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Geometry
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Residual
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Frattini placement and the quasithin obstruction

The source residual is the actual O²(C_L(r)). It centralizes E = ⟨r,z⟩.
Tight embedding places C_G(r), hence E, in N_G(L′). Therefore a two-group
P contained in L′E has all its squares, and consequently its Frattini
subgroup, inside L′. A nonidentity Frattini element v with rv conjugate
to r under L then contradicts the product exclusion proved in EmptyCase.

For the cover case, an independent element of order three fixing the E₉
residual in N_G(E) would generate an elementary group of order 27 there.
The normalizer is a genuine two-local subgroup, so quasithinness excludes it.
The construction of that actor and the complementary GL₂(3) argument are
not premises silently discharged by these conditional deductions.

Source: Aschbacher–Smith 16.4.9(2), combined manuscript of 1 March 2004,
printed pp.1191–1192. Complement construction and its placement in L′E
through H′/K′ remain separate obligations.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The embedded two-residual Lᵣ = O²(C_L(r)). -/
abbrev residual (L : Subgroup G) (r : G) : Subgroup G :=
  ComponentTransfer.Intrinsic.centralizerTwoResidual L r

omit [Finite G] in
/-- The residual retains both its component and fixed-point containments. -/
theorem residual_le_centralizer (L : Subgroup G) (r : G) :
    residual L r ≤ L ⊓ centralizer ({r} : Set G) := map_subtype_le _

/-- Both marked involutions centralize the actual residual. -/
theorem residual_le_fourGroup_centralizer (h : IntersectionSetup T z L g R) :
    residual L r ≤ centralizer (fourGroup r z : Set G) := by
  apply le_centralizer_iff.mpr
  apply sup_le
  · apply zpowers_le.mpr
    intro d hd
    exact mem_centralizer_singleton_iff.mp ((residual_le_centralizer L r hd).2)
  · apply zpowers_le.mpr
    intro d hd
    exact mem_centralizer_singleton_iff.mp (h.component.1 (residual_le_centralizer L r hd).1)

/-- Tight embedding gives C_G(r) ≤ N_G(L′), with relative normality intact. -/
theorem actor_centralizer_le_conjugate_normalizer (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) :
    centralizer ({r} : Set G) ≤ normalizer (L.conjBy g : Set G) := by
  rw [← normalizers_eq_conjBy h.normalizers_eq g]
  have hr1 : r ≠ 1 := by intro hh; simp [hh] at hr2
  have hN := h.normalizer_le (zpowers_ne_bot.mpr hr1) (zpowers_le.mpr hr)
  rw [show (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) from
    map_centralizer_equiv _ (MulAut.conj g)] at hN
  apply le_trans ?_ hN
  have hh : centralizer ({r} : Set G) = centralizer (zpowers r : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hh]
  exact centralizer_le_normalizer _

/-- The actual E normalizes the conjugate component. -/
theorem fourGroup_le_conjugate_normalizer (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) :
    fourGroup r z ≤ normalizer (L.conjBy g : Set G) := by
  apply le_trans ?_ (actor_centralizer_le_conjugate_normalizer h hr hr2)
  apply sup_le
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  · apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))).symm

/-- The exponent-two quotient of L′E puts Φ(P) inside L′. -/
theorem frattini_le_conjugate_component (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    {P : Subgroup G} (hP : IsPGroup 2 P)
    (hplace : P ≤ L.conjBy g ⊔ fourGroup r z) :
    (frattini P).map P.subtype ≤ L.conjBy g := by
  let : IsElementaryAbelian 2 (fourGroup r z) := (fourGroup_elementary_card h hr hr2 hout).1
  have hnorm := fourGroup_le_conjugate_normalizer h hr hr2
  rw [map_le_iff_le_comap, hP.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  change (x : G) ^ 2 ∈ L.conjBy g
  have hx : (x : G) ∈ (L.conjBy g : Set G) * (fourGroup r z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hplace x.property
  obtain ⟨l, hl, e, he, hex⟩ := hx
  have hesq : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e he
  have hel : e * l * e⁻¹ ∈ L.conjBy g := (mem_normalizer_iff.mp (hnorm he) l).mp hl
  have heq : (x : G) ^ 2 = l * (e * l * e⁻¹) * e ^ 2 := by
    rw [← hex]
    simp [pow_two, mul_assoc]
  rw [heq, hesq, mul_one]
  exact (L.conjBy g).mul_mem hl hel

/-- The centerless terminal contradiction, conditional on the placed complement and its product. -/
theorem deltaZero_nonempty_of_frattini_product (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    {P : Subgroup G} (hP : IsPGroup 2 P)
    (hplace : P ≤ L.conjBy g ⊔ fourGroup r z)
    (hfix : P ≤ centralizer ({r} : Set G))
    {v l : G} (hv : v ∈ (frattini P).map P.subtype) (hv1 : v ≠ 1)
    (hl : l ∈ L) (hprod : MulAut.conj l r = r * v) :
    (deltaZero L).Nonempty := by
  by_contra hempty
  have hvL := frattini_le_conjugate_component h hr hr2 hout hP hplace hv
  have hvr : Commute r v :=
    (mem_centralizer_singleton_iff.mp (hfix (map_subtype_le _ hv))).symm
  have hcomm : Commute r (MulAut.conj l r) := by
    rw [hprod]
    exact (Commute.refl r).mul_right hvr
  have hne : MulAut.conj l r ≠ r := by
    intro he
    have hrv : r * v = r * 1 := by simpa only [mul_one] using hprod.symm.trans he
    exact hv1 (mul_left_cancel hrv)
  exact h.conjugate_involution_product_not_mem_component hsmall hempty hr hr2 hl
    hcomm hne hprod hvL

/-- The quasithin three-rank contradiction inside the genuine two-local N_G(E). -/
theorem no_independent_centralizing_three (h : IntersectionSetup T z L g R)
    (hqt : IsQuasithin G) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hD : IsElementaryAbelian 3 (residual L r)) (hcard : Nat.card (residual L r) = 9)
    {x : G} (hxN : x ∈ normalizer (fourGroup r z : Set G))
    (hx3 : orderOf x = 3) (hxD : x ∉ residual L r)
    (hfix : residual L r ≤ centralizer ({x} : Set G)) : False := by
  let N := normalizer (fourGroup r z : Set G)
  have hDN : residual L r ≤ N :=
    (residual_le_fourGroup_centralizer h).trans (centralizer_le_normalizer _)
  let D := (residual L r).subgroupOf N
  let xN : N := ⟨x, hxN⟩
  let : IsElementaryAbelian 3 (residual L r) := hD
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.subgroupOf hDN
  have hDx : D ≤ centralizer ({xN} : Set N) := by
    intro d hd
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hfix hd))
  have hxN3 : orderOf xN = 3 := (orderOf_coe xN).symm.trans hx3
  have hDc : Nat.card D = 3 ^ 2 := (Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv).trans hcard
  have hlo : 3 ≤ primeRank 3 N := IsElementaryAbelian.primeRank_ge_of_fixed_join D xN
    hxN3 hxD hDx hDc
  have hE := fourGroup_elementary_card h hr hr2 hout
  let : IsElementaryAbelian 2 (fourGroup r z) := hE.1
  have hEn : fourGroup r z ≠ ⊥ := by
    intro hh
    have hc := hE.2
    rw [hh, card_bot] at hc
    omega
  have hlocal : IsTwoLocal N := ⟨fourGroup r z, hEn, IsElementaryAbelian.isPGroup 2 _, rfl⟩
  have hhi := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt N hlocal 3
    (by decide) (by decide)
  omega

/-- With the source center/two-core equality, the nontrivial cover has
exactly the marked central subgroup of order two. This is not a four-cover. -/
theorem center_eq_zpowers_of_nontrivial_core (h : IntersectionSetup T z L g R)
    (hTC : commutingSylow T L = zpowers z)
    (hcenter : center L = pCore 2 L) (hcore : pCore 2 L ≠ ⊥) :
    (center L).map L.subtype = zpowers z := by
  let C := (center L).map L.subtype
  let H := normalizer (L : Set G)
  have hCL : C ≤ L := map_subtype_le _
  have hCH : C ≤ H := hCL.trans L.le_normalizer
  have hn : H ≤ normalizer (C : Set G) :=
    normalizer_le_normalizer_characteristic_image L (center L)
  have hp : IsPGroup 2 C := by
    change IsPGroup 2 ((center L).map L.subtype)
    rw [hcenter]
    exact pCore_isPGroup.map L.subtype
  have hcH := le_pCoreIn_of_normalizes hp hCH hn
  have hCT : C ≤ (T : Subgroup G) := by
    have hh := hcH.trans (pCoreIn_le_sylow H (T.subtype h.sylow_normalizes))
    change C ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from h.sylow_normalizes)] at hh
  have hCK : C ≤ centralizer (L : Set G) := by
    rintro c ⟨cL, hcL, rfl⟩ l hl
    exact congrArg Subtype.val (mem_center_iff.mp hcL ⟨l, hl⟩)
  have hCz : C ≤ zpowers z := hTC ▸ le_inf hCT hCK
  have hCn : C ≠ ⊥ := by
    intro hh
    apply hcore
    rw [← hcenter]
    exact (map_eq_bot_iff_of_injective _ L.subtype_injective).mp hh
  have hdiv : Nat.card C ∣ 2 := by
    have hh := card_dvd_of_le hCz
    simpa only [Nat.card_zpowers, h.involution] using hh
  have hcard : Nat.card C = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun hc => hCn (C.eq_bot_iff_card.mpr hc))
  exact eq_of_le_of_card_ge hCz (by rw [Nat.card_zpowers, h.involution, hcard])


end CFSG.Quasithin.Chapter16.Intersections.GraphField
