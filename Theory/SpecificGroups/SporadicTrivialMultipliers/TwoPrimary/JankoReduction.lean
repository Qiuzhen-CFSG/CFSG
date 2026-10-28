module

public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoLocal
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.Mathieu.SchurMultipliers
public import Theory.GroupTheory.CentralExtensionSections
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction
public import Theory.GroupTheory.PerfectCentralSupplement

/-!
# Reduction of the J4 two-primary kernel to two local calculations

The literal E2048.M24 subgroup has odd index 173067389. In a central
extension of this subgroup, a normal lift of its binary core lets us quotient
to a central extension of the actual M24 model. The already proved M24
multiplier theorem makes the derived kernel trivial. Central transfer then
excludes a perfect J4 double cover with such a normal lift.

Prime-kernel reduction gives the requested general two-primary conclusion,
and the last theorem composes the original center projection with its supplied
model equivalence. The elementary-preimage and invariant-complement calculations
remain explicit in these assembly theorems. Neither is asserted here, and this
module alone does not establish the J4 multiplier theorem.

Source: Aschbacher--Smith I.1.1--I.1.3, printed p.407, citing GLS3 Section 6.1;
the odd-index subgroup is the literal ATLAS J4G1-max1W1 subgroup.
-/

public section
open Subgroup PerfectCentralCovering
namespace Janko4.TwoPrimary
universe u

/-- The actual ATLAS local subgroup has odd index in the matrix carrier. -/
theorem local_index_odd : ¬ 2 ∣ Local.index := by
  rw [Cardinality.max1Subgroup_index]
  decide

variable {L : Type*} [Group L] [Finite L]

/-- A normal lift of the core removes the derived part of the central kernel.
The quotient is the actual M24 model, whose multiplier is already proved trivial. -/
theorem derived_kernel_eq_bot_of_normal_complement
    (q : L →* Local) (hq : Function.Surjective q) (hc : q.ker ≤ center L)
    (T : Subgroup L) [T.Normal] (hT : T.map q = Core) (hd : Disjoint q.ker T) :
    q.ker ⊓ _root_.commutator L = ⊥ := by
  let π := QuotientGroup.mk' T
  let p : L ⧸ T →* Sporadic.Mathieu.M24 :=
    QuotientGroup.lift T (mathieuProjection.comp q) (by
      intro t ht
      have hm : q t ∈ Core := hT ▸ (show q t ∈ T.map q from ⟨t, ht, rfl⟩)
      rw [← mathieuProjection_ker] at hm
      exact hm)
  have hp : Function.Surjective p := QuotientGroup.lift_surjective_of_surjective T _
    (mathieuProjection_surjective.comp hq) _
  have hpk : p.ker = q.ker.map π := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T y
    constructor
    · intro hx
      have hxK : q x ∈ Core := by
        rw [← mathieuProjection_ker]
        exact hx
      rw [← hT] at hxK
      obtain ⟨t, ht, htx⟩ := hxK
      refine ⟨x * t⁻¹, ?_, ?_⟩
      · change q (x * t⁻¹) = 1
        rw [map_mul, map_inv, htx, mul_inv_cancel]
      · have ht1 : π t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
        change π (x * t⁻¹) = π x
        rw [map_mul, map_inv, ht1, inv_one, mul_one]
    · rintro ⟨z, hz, he⟩
      rw [← he]
      change mathieuProjection (q z) = 1
      rw [show q z = 1 from hz, map_one]
  have hpc : p.ker ≤ center (L ⧸ T) := by
    rw [hpk]
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp (hc hz) x)
  let d := CentralExtension.derivedCover p hp hpc
  have hk : d.toMonoidHom.ker = ⊥ :=
    Sporadic.Mathieu.SchurMultipliers.m24_cover_kernel_eq_bot d
  apply bot_unique
  rintro x ⟨hx, hxd⟩
  have hπd : π x ∈ _root_.commutator (L ⧸ T) := by
    have hm := Subgroup.mem_map_of_mem π hxd
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective T)] at hm
    exact hm
  have hx1 : (⟨π x, hπd⟩ : _root_.commutator (L ⧸ T)) = 1 := by
    apply mem_bot.mp
    rw [← hk]
    change mathieuProjection (q x) = 1
    rw [show q x = 1 from hx, map_one]
  have hxT : x ∈ T := (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hx1)
  exact mem_bot.mpr (disjoint_def.mp hd hx hxT)

/-- Transfer contradicts a normal core complement in the literal local preimage
of a central double cover of J4. -/
theorem no_double_cover_of_normal_complement
    {E : Type*} [Group E] [Finite E] (f : Cover E Model)
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (T : Subgroup (Local.comap f.toMonoidHom)) [T.Normal]
    (hT : T.map (f.toMonoidHom.subgroupComap Local) = Core)
    (hd : Disjoint (f.toMonoidHom.subgroupComap Local).ker T) : False := by
  let : Group.IsPerfect E := f.isPerfect
  let H := Local.comap f.toMonoidHom
  let q := f.toMonoidHom.subgroupComap Local
  have hq : Function.Surjective q :=
    f.toMonoidHom.subgroupComap_surjective_of_surjective Local f.surjective
  have hqc : q.ker ≤ center H := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (f.ker_le_center (congrArg Subtype.val hx)) y)
  have hKM : f.toMonoidHom.ker ≤ H := by
    intro x hx
    change f.toMonoidHom x ∈ Local
    rw [MonoidHom.mem_ker.mp hx]
    exact Local.one_mem
  have hder : f.toMonoidHom.ker ≤ ⁅H, H⁆ :=
    central_pSubgroup_le_commutator H f.toMonoidHom.ker hKM f.ker_le_center
      (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hcard))
      (by simpa only [H, Subgroup.index_comap_of_surjective _ f.surjective]
        using local_index_odd)
  have hlocal := derived_kernel_eq_bot_of_normal_complement q hq hqc T hT hd
  have hbot : f.toMonoidHom.ker = ⊥ := by
    apply bot_unique
    intro x hx
    let y : H := ⟨x, hKM hx⟩
    have hy : y ∈ _root_.commutator H := by
      have hh := hder hx
      rw [← map_subtype_commutator] at hh
      obtain ⟨z, hz, hzx⟩ := hh
      exact (show z = y from Subtype.ext hzx) ▸ hz
    have hyq : y ∈ q.ker := Subtype.ext hx
    have hy1 : y = 1 := mem_bot.mp (hlocal ▸ (show y ∈ q.ker ⊓ _root_.commutator H from ⟨hyq,hy⟩))
    exact mem_bot.mpr (congrArg Subtype.val hy1)
  rw [hbot, Subgroup.card_bot] at hcard
  omega


/-- The two concrete local calculations exclude two from every perfect
central covering kernel, after reduction to a prime-order kernel. -/
theorem kernel_not_two_of_local_calculations
    (hsquares : ElementaryPreimageCalculation.{u})
    (hcomplement : InvariantComplementCalculation.{u})
    {E : Type u} [Group E] [Finite E] (f : Cover E Model) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  apply f.not_dvd_card_kernel_of_no_prime_kernel
  intro F _ _ d hd
  let q := localProjection d
  have hq : Function.Surjective q :=
    d.toMonoidHom.subgroupComap_surjective_of_surjective Local d.surjective
  have hqc : q.ker ≤ center (Local.comap d.toMonoidHom) := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (d.ker_le_center (congrArg Subtype.val hx)) y)
  have hk : Nat.card q.ker = 2 := (localProjection_kernel_card d).trans hd
  obtain ⟨T, hTn, hdisjoint, hT⟩ := hcomplement _ q hq hqc hk (hsquares _ q hq hqc hk)
  let : T.Normal := hTn
  exact no_double_cover_of_normal_complement d hd T hT hdisjoint

/-- The requested two-primary kernel rigidity, conditional on the two
independent local calculations. No multiplier of J4 is assumed. -/
theorem kernel_eq_bot_of_local_calculations
    (hsquares : ElementaryPreimageCalculation.{u})
    (hcomplement : InvariantComplementCalculation.{u})
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (h2 : IsPGroup 2 f.ker) : f.ker = ⊥ := by
  let c : Cover E Model := ⟨f, hf, inferInstance, hc⟩
  exact Subgroup.card_eq_one.mp (h2.card_eq_or_dvd.resolve_right
    (kernel_not_two_of_local_calculations hsquares hcomplement c))

/-- Literal center-quotient application. The map is e composed with the
original quotient projection and its kernel is the entire center. -/
theorem center_eq_bot_of_quotient_equiv_of_local_calculations
    (hsquares : ElementaryPreimageCalculation.{u})
    (hcomplement : InvariantComplementCalculation.{u})
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* Model) (h2 : IsPGroup 2 (center E)) : center E = ⊥ := by
  let f : E →* Model := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact hk ▸ kernel_eq_bot_of_local_calculations hsquares hcomplement f hf hk.le (hk.symm ▸ h2)

end Janko4.TwoPrimary
