module

public import Theory.Mathieu.M22.UniversalMultiplier.TwoRankSource.ElementaryKernel
public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting
public import Theory.Frattini.PGroup

/-!
# Cyclic two-kernels over native M₂₂

Quotient the actual central kernel by its Frattini subgroup. The resulting
perfect cover has an elementary kernel, whose order is at most two by the
global-fusion and native-hexad argument. A generator of this Frattini quotient
lifts to a generator of the original kernel. No numerical multiplier upper
bound or constructed cyclic-four cover is required.

Source: the M₂₂ exclusion in Aschbacher–Smith 12.7.5, printed p.840;
compare the multiplier statement I.1.3(4), printed p.407.
-/

public section
noncomputable section
open Subgroup PerfectCentralCovering Theory.GroupTheory
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M22UniversalMultiplier.TwoRankSource

/-- Every finite perfect central cover of native M₂₂ with two-group kernel has cyclic kernel. -/
theorem twoPrimary_kernel_isCyclic {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) (hp : IsPGroup 2 f.toMonoidHom.ker) :
    IsCyclic f.toMonoidHom.ker := by
  let C := f.toMonoidHom.ker
  let D : Subgroup E := (frattini C).map C.subtype
  have hD : D ≤ f.toMonoidHom.ker := map_subtype_le _
  let : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (f.ker_le_center (hD hx)) g, mul_inv_cancel_right]
    exact hx⟩
  let g := f.quotientKernelSubgroup D hD
  let qC : C →* g.toMonoidHom.ker :=
    ((QuotientGroup.mk' D).comp C.subtype).codRestrict _ (fun x => x.property)
  have hqC : Function.Surjective qC := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective D y.val
    have hfx : f.toMonoidHom x = 1 := by
      change g.toMonoidHom (QuotientGroup.mk' D x) = 1
      rw [hx]
      exact y.property
    exact ⟨⟨x, hfx⟩, Subtype.ext hx⟩
  have hker : qC.ker = frattini C := by
    apply Subgroup.ext
    intro x
    change qC x = 1 ↔ x ∈ frattini C
    constructor
    · intro hx
      have hm : QuotientGroup.mk' D x.val = 1 :=
        congrArg (fun y : g.toMonoidHom.ker => (y : E ⧸ D)) hx
      obtain ⟨z, hz, he⟩ := (QuotientGroup.eq_one_iff (N := D) x.val).mp hm
      have hzx : z = x := Subtype.ext he
      exact hzx ▸ hz
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := D) x.val).mpr ⟨x, hx, rfl⟩
  let e : C ⧸ frattini C ≃* g.toMonoidHom.ker :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qC hqC)
  let : Fact (IsPGroup 2 C) := ⟨hp⟩
  let : IsElementaryAbelian 2 (C ⧸ frattini C) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 g.toMonoidHom.ker := {
    toIsMulCommutative := ⟨⟨fun x y => e.symm.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply e.symm.injective
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (C ⧸ frattini C)) (e.symm x)) }
  have hcard := elementary_kernel_card_le_two g
  have hpos : 0 < Nat.card g.toMonoidHom.ker := Nat.card_pos
  have hdiv : Nat.card g.toMonoidHom.ker ∣ 2 := by
    have hh : Nat.card g.toMonoidHom.ker = 1 ∨ Nat.card g.toMonoidHom.ker = 2 := by omega
    rcases hh with hh | hh
    · simpa only [hh] using (one_dvd (2 : ℕ))
    · simpa only [hh] using (dvd_refl (2 : ℕ))
  let : IsCyclic g.toMonoidHom.ker := isCyclic_of_card_dvd_prime hdiv
  let : IsCyclic (C ⧸ frattini C) := e.isCyclic.mpr inferInstance
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (C ⧸ frattini C))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (frattini C) x
  have hm : (zpowers a).map (QuotientGroup.mk' (frattini C)) = ⊤ := by
    simpa only [MonoidHom.map_zpowers] using hx
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨a, frattini_nongenerating ?_⟩
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using
    congrArg (Subgroup.comap (QuotientGroup.mk' (frattini C))) hm

end Sporadic.Mathieu.M22UniversalMultiplier.TwoRankSource
