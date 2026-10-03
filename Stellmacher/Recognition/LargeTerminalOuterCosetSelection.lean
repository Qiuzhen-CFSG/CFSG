module

public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalCoreInvolutionResidual
public import Theory.GroupAction.Order512FiveInvolutionCosets

/-!
# Selecting the derived coset of an outer core involution

Write R for the first residual, D for its derived subgroup, Q for the second
core, and Q₀ = C_Q(D). The supplied order-five subgroup acts on R/D. Its
fifteen nonidentity cosets contain exactly five cosets admitting involutory
lifts, and all five are conjugate under the supplied subgroup.

The intrinsic order-512 structure and the Frattini involution obstruction
prove this residual census. The core involution confinement theorem then
transports the census to Q/Q₀ and selects Df for every involution outside Q₀,
with conjugator in the supplied five-subgroup. The identity Q₀ ∩ R = D also
excludes involutions from Q₀f outside Df. No ambient Sylow-five or fusion
hypothesis is used.

Source: Thompson VI, PDF p.59, printed p.630, the five involutory cosets.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven Subgroup
universe u

private theorem residual_fixed_center
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    letI := conjMulDistribMulActionOfLeNormalizer A ctx.firstResidual hAN
    FixedPoints.subgroup A ctx.firstResidual ≤ center ctx.firstResidual := by
  let _ := conjMulDistribMulActionOfLeNormalizer A ctx.firstResidual hAN
  intro r hr
  apply hfixed
  change (r : G) ∈ centralizer (A : Set G)
  rw [mem_centralizer_iff]
  intro a ha
  have heq := congrArg ctx.firstResidual.subtype (hr ⟨a, ha⟩)
  change a * (r : G) * a⁻¹ = (r : G) at heq
  exact mul_inv_eq_iff_eq_mul.mp heq

/-- The residual quotient has fifteen nonidentity cosets, exactly five
of which admit involutory lifts. -/
public theorem LargeTerminalContext.residual_involutory_coset_census
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2) :
    let R := ctx.firstResidual
    let D := commutator R
    ({x : R ⧸ D | x ≠ 1}).ncard = 15 ∧
      {x : R ⧸ D | x ≠ 1 ∧ ∃ r : R,
        r ^ 2 = 1 ∧ QuotientGroup.mk' D r = x}.ncard = 5 := by
  let R := ctx.firstResidual
  let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := 9) ctx.first_residual_structure.1
  let b : R := ⟨f, hfR⟩
  have hb : b ^ 2 = 1 := Subtype.ext (hf ▸ pow_orderOf_eq_one f)
  have hbD : b ∉ commutator R := by
    intro h
    let _ := ctx.derived_residual_elementary
    exact hfc (le_centralizer (DerivedAmbient R) (mem_map_of_mem R.subtype h))
  have hh := Theory.GroupAction.parrott_involutory_derived_coset_census
    hR ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge
    hA (residual_fixed_center ctx A hAN hfixed) b hb hbD
  refine ⟨?_, hh.1⟩
  have hcard : Nat.card (R ⧸ commutator R) = 16 := by
    have hc := (commutator R).index_mul_card
    rw [ctx.first_residual_structure.2.2.2.2.1, ctx.first_residual_structure.1] at hc
    change Nat.card (R ⧸ commutator R) * 32 = 512 at hc
    omega
  change (({1} : Set (R ⧸ commutator R))ᶜ).ncard = 15
  rw [Set.ncard_compl, hcard, Set.ncard_singleton]

/-- Inside the residual, conjugation by the supplied five-subgroup selects
the distinguished derived coset. -/
public theorem LargeTerminalContext.residual_involution_coset_selection
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2)
    (x : G) (hxR : x ∈ ctx.firstResidual)
    (hxc : x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hx : orderOf x = 2) :
    ∃ a : G, a ∈ A ∧ (MulAut.conj a x) * f⁻¹ ∈ DerivedAmbient ctx.firstResidual := by
  let R := ctx.firstResidual
  let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := 9) ctx.first_residual_structure.1
  let b : R := ⟨f, hfR⟩
  let v : R := ⟨x, hxR⟩
  have hb : b ^ 2 = 1 := Subtype.ext (hf ▸ pow_orderOf_eq_one f)
  have hv : v ^ 2 = 1 := Subtype.ext (hx ▸ pow_orderOf_eq_one x)
  let _ := ctx.derived_residual_elementary
  have hbD : b ∉ commutator R := fun h =>
    hfc (le_centralizer (DerivedAmbient R) (mem_map_of_mem R.subtype h))
  have hvD : v ∉ commutator R := fun h =>
    hxc (le_centralizer (DerivedAmbient R) (mem_map_of_mem R.subtype h))
  obtain ⟨a, ha⟩ := (Theory.GroupAction.parrott_involutory_derived_coset_census
    hR ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge
    hA (residual_fixed_center ctx A hAN hfixed) b hb hbD).2 v hv hvD
  have hmem : (a • v) / b ∈ commutator R := QuotientGroup.eq_iff_div_mem.mp ha
  refine ⟨a, a.property, ?_⟩
  have hm := mem_map_of_mem R.subtype hmem
  change ((a : G) * x * (a : G)⁻¹) / f ∈ DerivedAmbient R at hm
  simpa only [div_eq_mul_inv, MulAut.conj_apply] using hm

/-- The literal second core has fifteen cosets outside its derived
centralizer. This counts cosets without asserting involutory lifts. -/
public theorem LargeTerminalContext.derived_centralizer_nonidentity_coset_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    let Q := twoCoreIn ctx.second
    let Q₀ := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
    {x : Q ⧸ Q₀.subgroupOf Q | x ≠ QuotientGroup.mk (1 : Q)}.ncard = 15 := by
  let Q := twoCoreIn ctx.second
  let Q₀ := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  have hcard : Nat.card (Q ⧸ Q₀.subgroupOf Q) = 16 :=
    (ctx.derived_centralizer_card_and_index hS).2
  change (({QuotientGroup.mk (1 : Q)} : Set (Q ⧸ Q₀.subgroupOf Q))ᶜ).ncard = 15
  rw [Set.ncard_compl, hcard, Set.ncard_singleton]

/-- Within the distinguished centralizer coset, membership in the
residual is exactly membership in its distinguished derived coset. -/
public theorem LargeTerminalContext.derived_centralizer_coset_mem_derived_iff
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f : G) (hfR : f ∈ ctx.firstResidual)
    (x : G)
    (hcoset : x * f⁻¹ ∈ twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G)) :
    x * f⁻¹ ∈ DerivedAmbient ctx.firstResidual ↔ x ∈ ctx.firstResidual := by
  constructor
  · intro h
    have hh := ctx.firstResidual.mul_mem (map_subtype_le _ h) hfR
    simpa only [inv_mul_cancel_right] using hh
  · intro hx
    rw [← ctx.derived_centralizer_supplement.2]
    exact ⟨hcoset, ctx.firstResidual.mul_mem hx (ctx.firstResidual.inv_mem hfR)⟩

/-- Once noncentralizing core involutions are confined to the residual,
the supplied five-subgroup selects the distinguished derived coset.
This conditional interface also permits separate confinement proofs. -/
public theorem LargeTerminalContext.outer_involution_coset_selection_of_residual_containment
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hresidual : ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) →
      orderOf x = 2 → x ∈ ctx.firstResidual)
    (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2) :
    ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) →
      orderOf x = 2 →
      ∃ a : G, a ∈ A ∧ (MulAut.conj a x) * f⁻¹ ∈ DerivedAmbient ctx.firstResidual := by
  intro x hxQ hxc hx
  exact ctx.residual_involution_coset_selection A hA hAN hfixed f hfR hfc hf
    x (hresidual x hxQ hxc hx) hxc hx

/-- Every outer core involution can be moved into the distinguished derived
coset by the supplied subgroup of order five. -/
public theorem LargeTerminalContext.outer_involution_coset_selection
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2) :
    ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) →
      orderOf x = 2 →
      ∃ a : G, a ∈ A ∧ (MulAut.conj a x) * f⁻¹ ∈ DerivedAmbient ctx.firstResidual := by
  exact ctx.outer_involution_coset_selection_of_residual_containment A hA hAN hfixed
    (ctx.core_involution_mem_residual hS A hA hAN hcard hfixed hncyc) f hfR hfc hf

/-- The distinguished centralizer coset contains no involutions outside
the distinguished derived coset. -/
public theorem LargeTerminalContext.derived_centralizer_coset_involution_mem_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2)
    (x : G) (hx : orderOf x = 2)
    (hcoset : x * f⁻¹ ∈ twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G)) :
    x * f⁻¹ ∈ DerivedAmbient ctx.firstResidual := by
  have hRQ : ctx.firstResidual ≤ twoCoreIn ctx.second := by
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hxQ : x ∈ twoCoreIn ctx.second := by
    simpa only [inv_mul_cancel_right] using
      (twoCoreIn ctx.second).mul_mem hcoset.1 (hRQ hfR)
  have hfD : f ∉ DerivedAmbient ctx.firstResidual := by
    let _ := ctx.derived_residual_elementary
    exact fun h => hfc (le_centralizer _ h)
  apply (ctx.derived_centralizer_coset_mem_derived_iff f hfR x hcoset).mpr
  exact ctx.core_involution_mem_residual_of_residual_coset hS A hA hAN hcard hfixed
    hncyc f hfR hfD (hf ▸ pow_orderOf_eq_one f) x hxQ (hx ▸ pow_orderOf_eq_one x)
    (by simpa only [div_eq_mul_inv] using hcoset)

/-- Of the fifteen nonidentity cosets of the derived centralizer in the
second core, exactly five admit involutory lifts. -/
public theorem LargeTerminalContext.outer_involutory_coset_census
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2) :
    let Q := twoCoreIn ctx.second
    let Q₀ := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
    {w : Q ⧸ Q₀.subgroupOf Q | w ≠ QuotientGroup.mk (1 : Q)}.ncard = 15 ∧
      {w : Q ⧸ Q₀.subgroupOf Q | w ≠ QuotientGroup.mk (1 : Q) ∧
        ∃ x : Q, x ^ 2 = 1 ∧ QuotientGroup.mk x = w}.ncard = 5 := by
  classical
  let R := ctx.firstResidual
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient R
  let Q₀ := Q ⊓ centralizer (D : Set G)
  have hRQ : R ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  let i : R →* Q := inclusion hRQ
  have hmem (r : R) : i r ∈ Q₀.subgroupOf Q ↔ r ∈ commutator R := by
    change (r : G) ∈ Q₀ ↔ r ∈ commutator R
    have hh : (r : G) ∈ Q₀ ↔ (r : G) ∈ D := by
      rw [show D = DerivedAmbient ctx.firstResidual from rfl,
        ← ctx.derived_centralizer_supplement.2]
      exact (and_iff_left r.property).symm
    exact hh.trans (mem_map_iff_mem R.subtype_injective)
  let j : R ⧸ commutator R → Q ⧸ Q₀.subgroupOf Q :=
    Quotient.map' i (by
      intro r s hrs
      apply QuotientGroup.leftRel_apply.mpr
      simpa only [← map_inv, ← map_mul] using
        (hmem (r⁻¹ * s)).mpr (QuotientGroup.leftRel_apply.mp hrs))
  have hj (r : R) : j (QuotientGroup.mk' (commutator R) r) = QuotientGroup.mk (i r) := rfl
  have hjinj : Function.Injective j := by
    intro w v
    induction w using QuotientGroup.induction_on with | H r =>
      induction v using QuotientGroup.induction_on with | H s =>
        intro heq
        apply QuotientGroup.eq.mpr
        apply (hmem (r⁻¹ * s)).mp
        simpa only [map_mul, map_inv] using QuotientGroup.eq.mp heq
  have hjone : j 1 = QuotientGroup.mk (1 : Q) := rfl
  let T := {w : R ⧸ commutator R | w ≠ 1 ∧
    ∃ r : R, r ^ 2 = 1 ∧ QuotientGroup.mk' (commutator R) r = w}
  let U := {w : Q ⧸ Q₀.subgroupOf Q | w ≠ QuotientGroup.mk (1 : Q) ∧
    ∃ x : Q, x ^ 2 = 1 ∧ QuotientGroup.mk x = w}
  have himage : j '' T = U := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨fun heq => hv.1 (hjinj (heq.trans hjone.symm)), ?_⟩
      obtain ⟨r, hr, rfl⟩ := hv.2
      exact ⟨i r, by rw [← map_pow, hr, map_one], hj r |>.symm⟩
    · rintro ⟨hw, x, hx, rfl⟩
      have hxC : (x : G) ∉ centralizer (D : Set G) := by
        intro hc
        apply hw
        apply QuotientGroup.eq.mpr
        simpa only [mul_one] using
          (Q₀.subgroupOf Q).inv_mem (show x ∈ Q₀.subgroupOf Q from ⟨x.property, hc⟩)
      have hxorder : orderOf (x : G) = 2 := by
        apply orderOf_eq_prime_iff.mpr
        refine ⟨congrArg Q.subtype hx, ?_⟩
        intro hxone
        exact hxC (hxone ▸ (centralizer (D : Set G)).one_mem)
      have hxR := ctx.core_involution_mem_residual hS A hA hAN hcard hfixed hncyc
        x x.property hxC hxorder
      let r : R := ⟨x, hxR⟩
      refine ⟨QuotientGroup.mk' (commutator R) r, ⟨?_, r, Subtype.ext
        (congrArg Q.subtype hx), rfl⟩, rfl⟩
      intro heq
      exact hw ((congrArg j heq).trans hjone)
  refine ⟨ctx.derived_centralizer_nonidentity_coset_card hS, ?_⟩
  change U.ncard = 5
  rw [← himage, Set.ncard_image_of_injective _ hjinj]
  exact (ctx.residual_involutory_coset_census A hA hAN hfixed f hfR hfc hf).2

end Stellmacher.Recognition
