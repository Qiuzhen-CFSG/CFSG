module

public import Stellmacher.Recognition.LargeTerminalFiveFixedConjugateGeometry
public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Theory.GroupAction.CentralDisplacement
public import Theory.GroupAction.Order512FiveOrbit
public import Theory.GroupTheory.FrattiniInvolutionObstruction
public import Theory.GroupAction.FrattiniInvertedCosets
public import Theory.Frattini.PGroup
public import Stellmacher.Recognition.LargeTerminalResidualQuotientAction
public import Stellmacher.Recognition.LargeTerminalResidualQuotientOrbitCensus

/-!
# Confining outer-core involutions to the residual

Write R for the first residual, D for its derived subgroup, Q for the
second local core, and Q₀ for the centralizer of D in Q. A five-fixed
involution y outside R centralizes D and has C_R(y) = D.

Conjugation by y cannot have central displacement at any element outside
D: the five-orbit of that element generates R, so central displacement
would propagate to all of R and bound [R : C_R(y)] by |Z(R)|. This
excludes involutions outside R in any Q₀-coset already containing a
residual involution. The inverted-lift Frattini obstruction bounds the
outer involutory residual cosets by nine, and conjugation by the second
local group preserves this set. The native orbit census supplies an
involutory residual lift for every nonidentity orbit of size less than ten.
Together these facts confine every core involution not centralizing D to R.

Source: Thompson, N-groups VI, PDF p.59, printed p.630, the exclusion
of involutions in Q₀F₁ outside DF₁.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven SevenSix SectionNine Subgroup
universe u

/-- A five-fixed element outside the residual has noncentral displacement
at every residual element outside the derived subgroup. -/
public theorem LargeTerminalContext.five_fixed_displacement_not_central
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (b : G) (hbR : b ∈ ctx.firstResidual) (hbD : b ∉ DerivedAmbient ctx.firstResidual) :
    y * b * y⁻¹ / b ∉ CenterAmbient ctx.firstResidual := by
  let R := ctx.firstResidual
  let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
  have hyN : y ∈ normalizer (R : Set G) :=
    ctx.second_le_residual_normalizer (twoCoreIn_le ctx.second hyQ)
  let e : MulAut R := R.normalizerMonoidHom ⟨y, hyN⟩
  let v : R := ⟨b, hbR⟩
  have hfixed' : FixedPoints.subgroup A R ≤ center R := by
    intro r hr
    apply hfixed
    change (r : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have heq := congrArg R.subtype (hr ⟨a, ha⟩)
    change a * (r : G) * a⁻¹ = (r : G) at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  have hvD : v ∉ commutator R :=
    fun h => hbD (mem_map_of_mem R.subtype h)
  have hgen := Theory.GroupAction.parrott_orbit_closure_eq_top
    (IsPGroup.of_card (p := 2) (n := 9) ctx.first_residual_structure.1)
    ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge
    hA hfixed' v hvD
  have hcomm (a : A) (r : R) : e (a • r) = a • e r := by
    apply Subtype.ext
    change y * ((a : G) * (r : G) * (a : G)⁻¹) * y⁻¹ =
      (a : G) * (y * (r : G) * y⁻¹) * (a : G)⁻¹
    have ha : Commute (a : G) y := mem_centralizer_iff.mp hyA a a.property
    calc
      _ = (y * a) * r * (y * a)⁻¹ := by group
      _ = (a * y) * r * (a * y)⁻¹ := by rw [ha.eq]
      _ = _ := by group
  have hFix : FixedPoints.subgroup (zpowers e) R = commutator R := by
    ext r
    rw [MulAut.mem_fixed_zpowers_iff]
    have hmem : (r : G) ∈ DerivedAmbient R ↔ r ∈ commutator R := by
      change (r : G) ∈ (commutator R).map R.subtype ↔ _
      exact mem_map_iff_mem R.subtype_injective
    rw [← hmem, ← ctx.five_fixed_residual_centralizer_eq_derived A hA hAN hfixed y hyQ hyA hyR]
    change e r = r ↔ (r : G) ∈ R ∧ (r : G) ∈ centralizer ({y} : Set G)
    rw [and_iff_right r.property, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hh := congrArg R.subtype h
      change y * (r : G) * y⁻¹ = r at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro h
      apply Subtype.ext
      change y * (r : G) * y⁻¹ = r
      exact mul_inv_eq_iff_eq_mul.mpr h.symm
  intro hcentral
  have hv : e v / v ∈ center R := by
    have hh : (↑(e v / v) : G) ∈ (center R).map R.subtype := hcentral
    exact (mem_map_iff_mem R.subtype_injective).mp hh
  have hle := Theory.GroupAction.index_fixed_le_card_center_of_central_displacement e
    (Theory.GroupAction.central_displacement_of_commuting_orbit_generator v hgen e hcomm hv)
  rw [hFix, ctx.first_residual_structure.2.2.2.1] at hle
  have hc := (commutator R).index_mul_card
  rw [ctx.first_residual_structure.2.2.2.2.1, ctx.first_residual_structure.1] at hc
  omega

/-- An involution in a derived-centralizer coset containing a residual
involution already belongs to the residual. -/
public theorem LargeTerminalContext.core_involution_mem_residual_of_residual_coset
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfD : f ∉ DerivedAmbient ctx.firstResidual) (hf : f ^ 2 = 1)
    (x : G) (hxQ : x ∈ twoCoreIn ctx.second) (hx : x ^ 2 = 1)
    (hcoset : x / f ∈ twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G)) :
    x ∈ ctx.firstResidual := by
  classical
  let Q := twoCoreIn ctx.second
  let R := ctx.firstResidual
  let D := DerivedAmbient R
  let Q₀ := Q ⊓ centralizer (D : Set G)
  obtain ⟨y, hyQ, hyA, hyR, hy⟩ :=
    ctx.exists_five_fixed_involution_of_not_cyclic A hcard hfixed hncyc
  have hyC := ctx.five_fixed_centralizes_derived A hA hAN hfixed y hyQ hyA
  have hy₀ : y ∈ Q₀ := ⟨hyQ, hyC⟩
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hRQ : R ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hQcard : Nat.card Q = 1024 := by
    obtain ⟨z, _, _, heq, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← heq]
    exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hc
  have hindex : (R.subgroupOf Q).index = 2 := by
    have hh := (R.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv,
      ctx.first_residual_structure.1, hQcard] at hh
    omega
  by_contra hxR
  have hrR : y * x ∈ R := by
    exact (mul_mem_iff_of_index_two (H := R.subgroupOf Q) hindex
      (a := ⟨y, hyQ⟩) (b := ⟨x, hxQ⟩)).mpr (iff_of_false hyR hxR)
  let r : R := ⟨y * x, hrR⟩
  let b : R := ⟨f, hfR⟩
  have hrD : y * x / f ∈ D := by
    change y * x / f ∈ DerivedAmbient ctx.firstResidual
    rw [← ctx.derived_centralizer_supplement.2]
    refine ⟨?_, R.div_mem hrR hfR⟩
    change y * x / f ∈ Q₀
    simpa only [div_eq_mul_inv, mul_assoc] using Q₀.mul_mem hy₀ hcoset
  have hrcoset : QuotientGroup.mk' (commutator R) r =
      QuotientGroup.mk' (commutator R) b := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact (mem_map_iff_mem R.subtype_injective).mp hrD
  have hfixed' : letI := conjMulDistribMulActionOfLeNormalizer A R hAN
      FixedPoints.subgroup A R ≤ center R := by
    let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
    intro a ha
    apply hfixed
    change (a : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro c hc
    have he := congrArg R.subtype (ha ⟨c, hc⟩)
    change c * (a : G) * c⁻¹ = a at he
    exact mul_inv_eq_iff_eq_mul.mp he
  let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
  obtain ⟨_, _, _, hUpper, hD, _⟩ := Theory.GroupAction.parrott_twoGroup_structure
    (IsPGroup.of_card (p := 2) (n := 9) ctx.first_residual_structure.1)
    ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge hA hfixed'
  let _ := hD
  have hr2 : r ^ 2 ∈ center R := square_mem_center_of_involutory_coset
    (commutator R) hUpper.le r b (Subtype.ext hf) hrcoset
  have hrnot : y * x ∉ D := by
    intro hr
    apply hfD
    have hh := D.mul_mem (D.inv_mem hrD) hr
    have heq : (y * x / f)⁻¹ * (y * x) = f := by
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rwa [heq] at hh
  apply ctx.five_fixed_displacement_not_central A hA hAN hfixed y hyQ hyA hyR
    (y * x) hrR hrnot
  have hh := mem_map_of_mem R.subtype ((center R).inv_mem hr2)
  change ((y * x) ^ 2)⁻¹ ∈ CenterAmbient R at hh
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy2)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have heq : y * (y * x) * y⁻¹ / (y * x) = ((y * x) ^ 2)⁻¹ := by
    simp only [div_eq_mul_inv, pow_two, mul_inv_rev, hyinv, hxinv]
    have hyy : y * y = 1 := by simpa only [pow_two] using hy2
    simp only [← mul_assoc, hyy, one_mul]
  rwa [heq]

/-- Fewer than ten nonidentity residual cosets admit a lift inverted
by a five-fixed core element. -/
public theorem LargeTerminalContext.five_fixed_inverted_residual_cosets_lt_ten
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) :
    {w : ctx.firstResidual ⧸ commutator ctx.firstResidual | w ≠ 1 ∧
      ∃ r : ctx.firstResidual, y * (r : G) * y⁻¹ = (r : G)⁻¹ ∧
        QuotientGroup.mk' (commutator ctx.firstResidual) r = w}.ncard < 10 := by
  let R := ctx.firstResidual
  let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
  have hfixed' : FixedPoints.subgroup A R ≤ center R := by
    intro r hr
    apply hfixed
    change (r : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have heq := congrArg R.subtype (hr ⟨a, ha⟩)
    change a * (r : G) * a⁻¹ = (r : G) at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := 9) ctx.first_residual_structure.1
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 R) := ⟨hR⟩
  obtain ⟨_, _, hPhi, hUpper, hD, hDcard⟩ :=
    Theory.GroupAction.parrott_twoGroup_structure hR ctx.first_residual_structure.1
      ctx.first_residual_structure.2.2.2.2.2.ge hA hfixed'
  let _ : IsElementaryAbelian 2 (commutator R) := hD
  let _ : IsElementaryAbelian 2 (R ⧸ commutator R) := by
    refine {
      toIsMulCommutative := (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := commutator R)).mpr le_rfl
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro w
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (commutator R) w
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (N := commutator R) _).mpr
    rw [hPhi]
    exact pth_power_mem_frattini_of_isPGroup (p := 2) r
  have hcard : Nat.card (R ⧸ commutator R) = 16 := by
    have hh := (commutator R).index_mul_card
    change Nat.card (R ⧸ commutator R) * Nat.card (commutator R) = Nat.card R at hh
    rw [hDcard, ctx.first_residual_structure.1] at hh
    omega
  have hyN := ctx.second_le_residual_normalizer (twoCoreIn_le ctx.second hyQ)
  let e : MulAut R := R.normalizerMonoidHom ⟨y, hyN⟩
  have hyD := ctx.five_fixed_centralizes_derived A hA hAN hfixed y hyQ hyA
  have he (r : R) (hr : r ∈ commutator R) : e r = r := by
    apply Subtype.ext
    change y * (r : G) * y⁻¹ = r
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (mem_centralizer_iff.mp hyD r (mem_map_of_mem R.subtype hr)).symm
  have hh := Theory.GroupAction.nonidentity_inverted_cosets_ncard_lt_ten
    (commutator R) hPhi hUpper hcard e he
  have heq : {w : R ⧸ commutator R | w ≠ 1 ∧
      ∃ r : R, e r = r⁻¹ ∧ QuotientGroup.mk' (commutator R) r = w} =
    {w : R ⧸ commutator R | w ≠ 1 ∧
      ∃ r : R, y * (r : G) * y⁻¹ = (r : G)⁻¹ ∧
        QuotientGroup.mk' (commutator R) r = w} := by
    ext w
    constructor
    · rintro ⟨hw, r, hr, hq⟩
      exact ⟨hw, r, congrArg R.subtype hr, hq⟩
    · rintro ⟨hw, r, hr, hq⟩
      exact ⟨hw, r, Subtype.ext hr, hq⟩
  rwa [heq] at hh

/-- Fewer than ten nonidentity residual cosets contain an involution
in the translate by a five-fixed involution. -/
public theorem LargeTerminalContext.five_fixed_outer_involutory_cosets_lt_ten
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hy : y ^ 2 = 1) :
    {w : ctx.firstResidual ⧸ commutator ctx.firstResidual | w ≠ 1 ∧
      ∃ r : ctx.firstResidual, (y * (r : G)) ^ 2 = 1 ∧
        QuotientGroup.mk' (commutator ctx.firstResidual) r = w}.ncard < 10 := by
  apply lt_of_le_of_lt (Set.ncard_le_ncard ?_)
    (ctx.five_fixed_inverted_residual_cosets_lt_ten A hA hAN hfixed y hyQ hyA)
  rintro w ⟨hw, r, hr, hq⟩
  refine ⟨hw, r, ?_, hq⟩
  have hyr : (y * (r : G))⁻¹ = y * r :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy)
  rw [hyi]
  calc
    y * (r : G) * y = (y * (r : G))⁻¹ * y := congrArg (fun t : G => t * y) hyr.symm
    _ = (r : G)⁻¹ := by rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

/-- Every native orbit of an outer involutory residual coset consists
of outer involutory residual cosets, using the same five-fixed involution. -/
public theorem LargeTerminalContext.core_involution_residual_orbit_lifts
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (hy : y ^ 2 = 1)
    (r : ctx.firstResidual) (hr : (y * (r : G)) ^ 2 = 1)
    (g : ctx.second) :
    ∃ r' : ctx.firstResidual, (y * (r' : G)) ^ 2 = 1 ∧
      QuotientGroup.mk' (commutator ctx.firstResidual) r' =
        ctx.residualQuotientAction g (QuotientGroup.mk' (commutator ctx.firstResidual) r) := by
  let R := ctx.firstResidual
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient R
  let Q₀ := Q ⊓ centralizer (D : Set G)
  have hRQ : R ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hi : (R.subgroupOf Q).index = 2 := by
    obtain ⟨z, _, _, heq, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    have hQcard : Nat.card Q = 1024 := by
      change Nat.card (twoCoreIn ctx.second) = 1024
      rw [← heq]
      exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hc
    have hh := (R.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv,
      ctx.first_residual_structure.1, hQcard] at hh
    omega
  let e := MulAut.conj (g : G)
  have hy₀ : y ∈ Q₀ := ⟨hyQ, ctx.five_fixed_centralizes_derived A hA hAN hfixed y hyQ hyA⟩
  have hg₀ : (g : G) ∈ normalizer (Q₀ : Set G) :=
    (ctx.derived_centralizer_normalizer_local_data hS).2.1 g.property
  have hey₀ : e y ∈ Q₀ := (mem_normalizer_iff.mp hg₀ y).mp hy₀
  have hgR := ctx.second_le_residual_normalizer g.property
  have heyR : e y ∉ R := fun hh => hyR ((mem_normalizer_iff.mp hgR y).mpr hh)
  have hdR : y * e y ∈ R :=
    (mul_mem_iff_of_index_two (H := R.subgroupOf Q) hi
      (a := ⟨y, hyQ⟩) (b := ⟨e y, hey₀.1⟩)).mpr (iff_of_false hyR heyR)
  have hdD : y * e y ∈ D := by
    change y * e y ∈ DerivedAmbient ctx.firstResidual
    rw [← ctx.derived_centralizer_supplement.2]
    exact ⟨Q₀.mul_mem hy₀ hey₀, hdR⟩
  let d : R := ⟨y * e y, hdR⟩
  let s : R := ⟨e r, (mem_normalizer_iff.mp hgR r).mp r.property⟩
  refine ⟨d * s, ?_, ?_⟩
  · have heq : y * (↑(d * s) : G) = e (y * r) := by
      change y * ((y * e y) * e r) = e (y * r)
      rw [map_mul]
      have hy2 : y * y = 1 := by simpa only [pow_two] using hy
      simp only [← mul_assoc, hy2, one_mul]
    rw [heq, ← map_pow, hr, map_one]
  · have hd : d ∈ commutator R := (mem_map_iff_mem R.subtype_injective).mp hdD
    have hqd : QuotientGroup.mk' (commutator R) d = 1 :=
      (QuotientGroup.eq_one_iff (N := commutator R) d).mpr hd
    change QuotientGroup.mk' (commutator R) (d * s) = _
    rw [map_mul, hqd, one_mul]
    exact (ctx.residualQuotientAction_apply_mk g r s rfl).symm

/-- The small-orbit lift assertion, together with the two exclusions,
confines every core involution
not centralizing the derived residual to the residual itself. -/
public theorem LargeTerminalContext.core_involution_mem_residual_of_small_orbit_lifts
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (hlift : ∀ w : ctx.firstResidual ⧸ commutator ctx.firstResidual, w ≠ 1 →
      (Set.range (fun g : ctx.second => ctx.residualQuotientAction g w)).ncard < 10 →
      ∃ f : ctx.firstResidual, f ^ 2 = 1 ∧
        QuotientGroup.mk' (commutator ctx.firstResidual) f = w) :
    ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) →
      orderOf x = 2 → x ∈ ctx.firstResidual := by
  intro x hxQ hxC hx
  by_contra hxR
  let R := ctx.firstResidual
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient R
  let Q₀ := Q ⊓ centralizer (D : Set G)
  obtain ⟨y, hyQ, hyA, hyR, hy⟩ :=
    ctx.exists_five_fixed_involution_of_not_cyclic A hcard hfixed hncyc
  have hyC := ctx.five_fixed_centralizes_derived A hA hAN hfixed y hyQ hyA
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyy : y * y = 1 := by simpa only [pow_two] using hy2
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hRQ : R ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hi : (R.subgroupOf Q).index = 2 := by
    obtain ⟨z, _, _, heq, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    have hQcard : Nat.card Q = 1024 := by
      change Nat.card (twoCoreIn ctx.second) = 1024
      rw [← heq]
      exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hc
    have hh := (R.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv,
      ctx.first_residual_structure.1, hQcard] at hh
    omega
  have hrR : y * x ∈ R :=
    (mul_mem_iff_of_index_two (H := R.subgroupOf Q) hi
      (a := ⟨y, hyQ⟩) (b := ⟨x, hxQ⟩)).mpr (iff_of_false hyR hxR)
  let r : R := ⟨y * x, hrR⟩
  have hyr : y * (r : G) = x := by
    change y * (y * x) = x
    rw [← mul_assoc, hyy, one_mul]
  have hr : (y * (r : G)) ^ 2 = 1 := hyr.symm ▸ hx2
  let q := QuotientGroup.mk' (commutator R)
  have hrD : r ∉ commutator R := by
    intro hh
    have hrC : (r : G) ∈ centralizer (D : Set G) := by
      let _ := ctx.derived_residual_elementary
      exact le_centralizer D (mem_map_of_mem R.subtype hh)
    exact hxC (hyr ▸ (centralizer (D : Set G)).mul_mem hyC hrC)
  have hqr : q r ≠ 1 := fun hh => hrD ((QuotientGroup.eq_one_iff r).mp hh)
  have hsmall : (Set.range (fun g : ctx.second => ctx.residualQuotientAction g (q r))).ncard < 10 := by
    apply lt_of_le_of_lt (Set.ncard_le_ncard ?_)
      (ctx.five_fixed_outer_involutory_cosets_lt_ten A hA hAN hfixed y hyQ hyA hy2)
    rintro w ⟨g, rfl⟩
    refine ⟨?_, ctx.core_involution_residual_orbit_lifts hS A hA hAN hfixed y
      hyQ hyA hyR hy2 r hr g⟩
    exact fun hh => hqr ((ctx.residualQuotientAction g).map_eq_one_iff.mp hh)
  obtain ⟨f, hf, hqf⟩ := hlift (q r) hqr hsmall
  have hfD : (f : G) ∉ D := by
    intro hh
    have hfd : f ∈ commutator R := (mem_map_iff_mem R.subtype_injective).mp hh
    apply hqr
    exact hqf.symm.trans ((QuotientGroup.eq_one_iff f).mpr hfd)
  have hrf : r / f ∈ commutator R := QuotientGroup.eq_iff_div_mem.mp hqf.symm
  have hrfD : (r : G) / (f : G) ∈ D := mem_map_of_mem R.subtype hrf
  have hcoset : x / (f : G) ∈ Q₀ := by
    have hD₀ : D ≤ Q₀ := by
      rw [show D = DerivedAmbient ctx.firstResidual from rfl,
        ← ctx.derived_centralizer_supplement.2]
      exact inf_le_left
    have hh := Q₀.mul_mem (show y ∈ Q₀ from ⟨hyQ, hyC⟩) (hD₀ hrfD)
    have heq : y * ((r : G) / (f : G)) = x / (f : G) := by
      rw [div_eq_mul_inv, ← mul_assoc, hyr, div_eq_mul_inv]
    rwa [heq] at hh
  exact hxR (ctx.core_involution_mem_residual_of_residual_coset hS A hA hAN hcard
    hfixed hncyc f f.property hfD (congrArg R.subtype hf) x hxQ hx2 hcoset)

/-- Every involution of the second local core that does not centralize the
derived residual belongs to the residual. The native orbit census supplies
the involutory lifts needed by the two exclusion arguments. -/
public theorem LargeTerminalContext.core_involution_mem_residual
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second))) :
    ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) →
      orderOf x = 2 → x ∈ ctx.firstResidual := by
  exact ctx.core_involution_mem_residual_of_small_orbit_lifts hS A hA hAN hcard
    hfixed hncyc ctx.residual_quotient_small_orbit_lifts

end Stellmacher.Recognition
