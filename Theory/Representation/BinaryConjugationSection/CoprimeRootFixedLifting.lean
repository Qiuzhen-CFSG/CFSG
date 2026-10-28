module

public import Theory.Representation.BinaryConjugationSection.CoprimeFixedCard
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# Lifting a root-fixed vector while retaining its coprime normalizer

Coprime fixed-point lifting supplies an actor-fixed representative. If the
root is fully moved by that actor, the three-subgroups lemma eliminates
its central displacement. Thus the representative centralizes the actual
root, not only its image on the binary section.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W]
    {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- A root-fixed vector with coprime-normalizer-fixed coordinates has a
representative centralizing both actual subgroups. -/
theorem exists_centralizing_root_lift (d : BinaryConjugationSection H U Z ρ)
    (A R : Subgroup G) (hAH : A≤H) (hRH : R≤H)
    (hsolv : Group.IsSolvable U) (hcop : Nat.Coprime (Nat.card A) (Nat.card U))
    (hmoved : ⁅R,A⁆=R) (hZA : Z≤centralizer (A:Set G))
    (w : W) (hwR : w∈fixedSpace ρ (R.subgroupOf H))
    (hwA : w∈fixedSpace ρ (A.subgroupOf H)) :
    ∃ u:U, (u:G)∈centralizer (A:Set G) ⊓ centralizer (R:Set G) ∧
      (d.coordinates u).toAdd=w := by
  let native := conjMulDistribMulActionOfLeNormalizer A U (hAH.trans d.normalized)
  let _ : MulDistribMulAction A U := native
  let _ : SMul A U := native.toSMul
  let _ : MulAction A U := native.toMulAction
  have hequiv (a:A) (u:U) :
      (d.coordinates (a • u)).toAdd=ρ (inclusion hAH a) (d.coordinates u).toAdd :=
    d.equivariant (inclusion hAH a) u
  have hInv : IsInvariant A U d.coordinates.ker := by
    constructor
    intro a u
    change d.coordinates u=1 ↔ d.coordinates (a • u)=1
    constructor
    · intro hu
      apply Multiplicative.toAdd.injective
      rw [hequiv,hu]
      exact map_zero _
    · intro hu
      have hh := congrArg Multiplicative.toAdd hu
      rw [hequiv] at hh
      apply Multiplicative.toAdd.injective
      exact (ρ.apply_bijective (inclusion hAH a)).injective (hh.trans (map_zero _).symm)
  let _ : MulDistribMulAction A (U ⧸ d.coordinates.ker) :=
    quotientMulDistribMulAction d.coordinates.ker hInv
  obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd w)
  have hq : QuotientGroup.mk' d.coordinates.ker u ∈
      FixedPoints.subgroup A (U ⧸ d.coordinates.ker) := by
    intro a
    change QuotientGroup.mk' d.coordinates.ker (a • u)=QuotientGroup.mk' d.coordinates.ker u
    apply QuotientGroup.eq_iff_div_mem.mpr
    change d.coordinates ((a • u)/u)=1
    rw [map_div,div_eq_one]
    apply Multiplicative.toAdd.injective
    rw [hequiv,hu]
    exact hwA ⟨inclusion hAH a,a.property⟩
  rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop _ hInv] at hq
  obtain ⟨v,hv,he⟩ := hq
  have hvA : (v:G)∈centralizer (A:Set G) := by
    intro a ha
    have hh := congrArg Subtype.val (hv ⟨a,ha⟩)
    change a*(v:G)*a⁻¹=(v:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hvw : (d.coordinates v).toAdd=w := by
    have hh := QuotientGroup.eq_iff_div_mem.mp he
    change d.coordinates (v/u)=1 at hh
    rw [map_div,div_eq_one] at hh
    exact congrArg Multiplicative.toAdd (hh.trans hu)
  have hUZ : U≤normalizer (Z:Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.kernel_le).mp d.kernel_normal
  have hvpre : (v:G)∈commutatorPreimage U R Z := by
    apply (mem_commutatorPreimage_iff U R Z hUZ _).mpr
    refine ⟨v.property,?_⟩
    intro r hr
    let rH : H := ⟨r,hRH hr⟩
    let t : U := ⟨r*(v:G)*r⁻¹,(mem_normalizer_iff.mp (d.normalized rH.property) v).mp v.property⟩
    have ht : (d.coordinates t).toAdd=w := by
      rw [d.equivariant rH v,hvw]
      exact hwR ⟨rH,hr⟩
    have hm : d.coordinates (t/v)=1 := by
      rw [map_div,div_eq_one]
      exact Multiplicative.toAdd.injective (ht.trans hvw.symm)
    have hh : ⁅r,(v:G)⁆∈Z := by
      simpa only [t,Subgroup.coe_div,div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv,Subtype.coe_mk,commutatorElement_def]
        using (d.coordinates_eq_one_iff (t/v)).mp hm
    simpa only [commutatorElement_inv] using Z.inv_mem hh
  have hZR : ⁅zpowers (v:G),R⁆≤Z :=
    (commutator_mono (zpowers_le.mpr hvpre) le_rfl).trans
      (commutator_commutatorPreimage_le U R Z hUZ)
  have hzero : ⁅⁅R,A⁆,zpowers (v:G)⁆=⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by rw [commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (zpowers_le.mpr hvA)),commutator_bot_left])
      (by
        apply bot_unique
        exact (commutator_mono hZR le_rfl).trans
          (commutator_eq_bot_iff_le_centralizer.mpr hZA).le)
  rw [hmoved,commutator_comm,commutator_eq_bot_iff_le_centralizer] at hzero
  exact ⟨v,⟨hvA,hzero (mem_zpowers (v:G))⟩,hvw⟩

end Representation.BinaryConjugationSection
