module

public import Theory.GroupTheory.PGroup.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence.ClassTwoOmega
public import Theory.GroupTheory.PGroup.SupercriticalExistence.Maximal
public import Theory.GroupTheory.PGroup.SupercriticalExistence.SecondCenterRoots
public import Theory.Frattini.PGroup

/-!
# Supercritical subgroups of finite odd-prime p-groups

Maximize a characteristic subgroup X of exponent dividing p with central
ambient commutators. It absorbs every characteristic exponent-p subgroup
of its centralizer C. In particular it absorbs first omega in the second
center of C. Consequently the p-th roots in that second center are central
in C. The odd-prime second-center root theorem then makes all p-th roots
in C central, and each such root is already in X, proving precisely the
supercritical centralizer condition.
The Frattini condition follows from its commutator-and-power description.

The conditional construction is retained as a separate interface. The
unconditional existence theorem discharges its root-propagation premise
using the second-center theorem proved from the mechanisms of Aschbacher's
(23.15)–(23.16). This constructs the required subgroup directly, including
for the trivial group under the exponent-divisibility convention.

Sources: Aschbacher, *Finite Group Theory*, (23.11), (23.16), and (24.9),
printed pp.110, 112, and 114; Aschbacher–Smith, *The Classification of
Quasithin Groups*, A.1.20–21, printed pp.24–25.
-/

open Subgroup
open scoped commutatorElement

namespace IsSupercriticalPSubgroup

/-- The trivial ambient group has its bottom subgroup as a supercritical
subgroup, using exponent divisibility rather than exact exponent. -/
public theorem bot_of_subsingleton
    {p : ℕ} {P : Type*} [Group P] [Subsingleton P] :
    IsSupercriticalPSubgroup p (⊥ : Subgroup P) := by
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact mem_center_iff.mpr (fun _ => Subsingleton.elim _ _)
  · simp
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun _ => Subsingleton.elim _ _)
  · intro x _ _
    exact mem_bot.mpr (Subsingleton.elim _ _)

end IsSupercriticalPSubgroup

namespace IsPGroup

/-- Supercritical existence reduced to propagation of central p-th roots
from the second center, applied to the centralizer of a maximal candidate.
The unconditional theorem below supplies the displayed implication. -/
public theorem exists_supercriticalPSubgroup_of_second_center
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hp : p ≠ 2)
    (hsecond : ∀ C : Subgroup P,
      (∀ c : C, c ∈ Subgroup.upperCentralSeries C 2 → c ^ p = 1 → c ∈ center C) →
      ∀ c : C, c ^ p = 1 → c ∈ center C) :
    ∃ X : Subgroup P, IsSupercriticalPSubgroup p X := by
  obtain ⟨X, hXchar, hXcomm, hXpow, hmax⟩ :=
    hP.exists_characteristic_exponent_subgroup_saturated
  let : X.Characteristic := hXchar
  let C := centralizer (X : Set P)
  let : C.Characteristic := inferInstance
  let D := Subgroup.upperCentralSeries C 2
  let : D.Characteristic := inferInstance
  let U := omega₁ D (p := p)
  let : U.Characteristic := omega₁_characteristic D
  let K₀ := U.map D.subtype
  let : K₀.Characteristic := inferInstance
  let K := K₀.map C.subtype
  let : K.Characteristic := inferInstance
  have hKpow : Monoid.exponent K ∣ p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨x, hx⟩
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hc
    have hdPow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (exponent_omega_one_second_center_dvd (G := C) hp) (⟨d, hd⟩ : U)
    exact Subtype.ext (congrArg (fun u : U => ((u : D) : C).val) hdPow)
  have hKX : K ≤ X := hmax K inferInstance hKpow (map_subtype_le K₀)
  have hrootK (c : C) (hc : c ∈ D) (hcp : c ^ p = 1) : (c : P) ∈ K := by
    apply mem_map_of_mem C.subtype
    apply mem_map_of_mem D.subtype (x := (⟨c, hc⟩ : D))
    apply subset_closure
    change (⟨c, hc⟩ : D) ^ (p ^ 1) = 1
    apply Subtype.ext
    change c ^ (p ^ 1) = 1
    simpa only [pow_one] using hcp
  have hcentral : ∀ c : C, c ^ p = 1 → c ∈ center C := by
    apply hsecond C
    intro c hc hcp
    have hcX := hKX (hrootK c hc hcp)
    apply mem_center_iff.mpr
    intro d
    exact Subtype.ext ((d.property (c : P) hcX).symm)
  have hderived : _root_.commutator X ≤ center X := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    have hm : ((⁅x, y⁆ : X) : P) ∈ (center X).map X.subtype :=
      hXcomm (commutator_mem_commutator x.property (mem_top (y : P)))
    obtain ⟨z, hz, he⟩ := hm
    exact (Subtype.ext he : z = ⁅x, y⁆) ▸ hz
  refine ⟨X, ⟨hXchar, ?_, hXcomm, hXpow, ?_⟩⟩
  · let : Fact (IsPGroup p X) := ⟨hP.to_subgroup X⟩
    rw [frattini_eq_closure_commutator_union_powers (p := p)]
    apply (closure_le _).mpr
    rintro x (hx | ⟨y, rfl⟩)
    · exact hderived hx
    · change y ^ p ∈ center X
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hXpow y]
      exact (center X).one_mem
  · intro x hx horder
    have hxp : (⟨x, hx⟩ : C) ^ p = 1 := by
      apply Subtype.ext
      change x ^ p = 1
      simpa only [horder] using pow_orderOf_eq_one x
    have hxc := hcentral ⟨x, hx⟩ hxp
    have hxD : (⟨x, hx⟩ : C) ∈ D :=
      (show center C ≤ D by
        simpa only [Subgroup.upperCentralSeries_one] using
          Subgroup.upperCentralSeries_mono C (show 1 ≤ 2 by decide)) hxc
    exact hKX (hrootK ⟨x, hx⟩ hxD hxp)

/-- Every finite p-group for an odd prime p has a supercritical subgroup,
including the order-p centralizer condition of Aschbacher–Smith A.1.20.
This proves the existence assertion of A.1.21(1). -/
public theorem exists_supercriticalPSubgroup
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hp : p ≠ 2) :
    ∃ X : Subgroup P, IsSupercriticalPSubgroup p X := by
  exact hP.exists_supercriticalPSubgroup_of_second_center hp
    (fun C => (hP.to_subgroup C).prime_roots_central_of_second_center hp)

end IsPGroup
