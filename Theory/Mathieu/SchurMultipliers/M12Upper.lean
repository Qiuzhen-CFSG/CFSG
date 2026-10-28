module

public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.Mathieu.SchurMultipliers.M12Upper.Fusion
public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound
public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation
public import Theory.GroupTheory.PerfectCentralCoverLocalBound

/-!
# The M₁₂ multiplier upper bound

The already proved odd-prime exclusion makes every perfect M₁₂ covering
kernel a two-group. Central transfer across the first parabolic's odd
index 495 identifies that entire kernel with the derived kernel of its
literal full preimage. Quaternion normality and the second-parabolic cubic
supply the commuting-lift relation required by `FirstParabolicLiftBound`.

The proved local calculation bounds that derived kernel by two, so every
finite perfect central cover of the actual M₁₂ has kernel of order at most
two. The calculation has the order-192 group as codomain, with no perfectness
assumption on its central extension. Constructing the nontrivial M₁₂ double
cover is a separate lower-bound problem.
Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407, citing GLS3 §6.1.
-/

namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open Subgroup M12SmallPair PerfectCentralCovering
universe u
variable {E : Type u} [Group E] [Finite E]

/-- The marked involution centralizer has odd index 495 in the actual M₁₂. -/
public theorem firstParabolic_index : firstParabolic.index = 495 := by
  have h := firstParabolic.card_mul_index
  rw [card_firstParabolic, m12_order] at h
  omega

/-- Transfer across the odd index identifies the entire global covering
kernel with the derived kernel of the literal first-parabolic preimage. -/
public theorem kernel_card_eq_firstParabolic_derived_kernel (f : Cover E M12) :
    Nat.card f.toMonoidHom.ker =
      Nat.card ((f.toMonoidHom.subgroupComap firstParabolic).ker ⊓
        _root_.commutator (firstParabolic.comap f.toMonoidHom) :
        Subgroup (firstParabolic.comap f.toMonoidHom)) := by
  let : Group.IsPerfect E := f.isPerfect
  let P := firstParabolic.comap f.toMonoidHom
  let q := f.toMonoidHom.subgroupComap firstParabolic
  have hKP : f.toMonoidHom.ker ≤ P := by
    intro x hx
    change f.toMonoidHom x ∈ firstParabolic
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hi : ¬ 2 ∣ P.index := by
    rw [show P.index = firstParabolic.index from
      index_comap_of_surjective _ f.surjective, firstParabolic_index]
    decide
  have hd := central_pSubgroup_le_commutator P f.toMonoidHom.ker hKP
    f.ker_le_center (m12_cover_kernel_isTwoGroup f) hi
  have hderived (x : f.toMonoidHom.ker) :
      (⟨x, hKP x.property⟩ : P) ∈ _root_.commutator P := by
    have hx := hd x.property
    rw [← map_subtype_commutator] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have heq : y = ⟨x, hKP x.property⟩ := Subtype.ext hxy
    exact heq ▸ hy
  let e : f.toMonoidHom.ker ≃* (q.ker ⊓ _root_.commutator P : Subgroup P) := {
    toFun x := ⟨⟨x, hKP x.property⟩, ⟨Subtype.ext x.property, hderived x⟩⟩
    invFun x := ⟨x.val.val, congrArg Subtype.val x.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact Nat.card_congr e.toEquiv

end Sporadic.Mathieu.SchurMultipliers.M12Upper

namespace Sporadic.Mathieu.SchurMultipliers
open Subgroup M12SmallPair PerfectCentralCovering M12Upper
universe u

/-- The remaining relative calculation, combined with the proved quaternion
fusion and transfer steps, bounds every finite perfect M12 covering kernel. -/
public theorem m12_cover_kernel_card_le_two_of_firstParabolic_bound
    (hlocal : FirstParabolicLiftBound.{u})
    {E : Type u} [Group E] [Finite E] (f : Cover E M12) :
    Nat.card f.toMonoidHom.ker ≤ 2 := by
  let : Group.IsPerfect E := f.isPerfect
  let P := firstParabolic.comap f.toMonoidHom
  let q : P →* firstParabolic := f.toMonoidHom.subgroupComap firstParabolic
  have hq : Function.Surjective q :=
    f.toMonoidHom.subgroupComap_surjective_of_surjective firstParabolic f.surjective
  have hqk {x : P} (hx : x ∈ q.ker) : (x : E) ∈ f.toMonoidHom.ker :=
    congrArg Subtype.val hx
  have hqc : q.ker ≤ center P := fun x hx => mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (f.ker_le_center (hqk hx)) y)
  let k : q.ker →* f.toMonoidHom.ker :=
    (P.subtype.comp q.ker.subtype).codRestrict _ (fun x => hqk x.property)
  have hki : Function.Injective k := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.toMonoidHom.ker => (z : E)) h))
  have hqp : IsPGroup 2 q.ker := (m12_cover_kernel_isTwoGroup f).of_injective k hki
  have hv : v ∈ firstParabolic := core_le_firstParabolic (natural_le_core v_mem_natural)
  have ht : third ∈ firstParabolic := core_le_firstParabolic (elementary_le_core
    (subset_closure (by simp)))
  obtain ⟨a, ha⟩ := hq ⟨v, hv⟩
  obtain ⟨b, hb⟩ := hq ⟨third, ht⟩
  have ha' : f.toMonoidHom (a : E) = v := congrArg Subtype.val ha
  have hb' : f.toMonoidHom (b : E) = third := congrArg Subtype.val hb
  have hab : Commute a b :=
    (commute_lifts_v_third f.toMonoidHom f.surjective f.ker_le_center
      (a : E) (b : E) ha' hb').of_map P.subtype_injective
  rw [kernel_card_eq_firstParabolic_derived_kernel f]
  exact hlocal P q hq hqc hqp ⟨a, b, ha', hb', hab⟩

/-- Every finite perfect central cover of the actual twelve-point Mathieu
group has kernel of order at most two. This is the upper bound in I.1.3(1). -/
public theorem m12_cover_kernel_card_le_two
    {E : Type u} [Group E] [Finite E] (f : Cover E M12) :
    Nat.card f.toMonoidHom.ker ≤ 2 :=
  m12_cover_kernel_card_le_two_of_firstParabolic_bound firstParabolicLiftBound f

end Sporadic.Mathieu.SchurMultipliers
