module

public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# The full quotient kernel of a literal binary conjugation section

If the actor map has kernel N, quotienting the actor by Z identifies its
full new kernel with N/Z. The equivalence uses the original subgroup
inclusion and quotient maps and intertwines the given conjugation section.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G D : Type*} [Group G] [Group D]

/-- The canonical N/Z coordinates identify the entire kernel in H/Z and
retain its actual conjugation action along the original actor map. -/
theorem exists_quotient_kernel_equiv
    (H N Z : Subgroup G) [(Z.subgroupOf H).Normal] [(Z.subgroupOf N).Normal]
    [IsElementaryAbelian 2 (N ⧸ Z.subgroupOf N)]
    (q : H →* D) (hq : Function.Surjective q) (hk : q.ker=N.subgroupOf H)
    (ρ : Representation (ZMod 2) D (Additive (N ⧸ Z.subgroupOf N)))
    (d : BinaryConjugationSection H N Z (ρ.comp q))
    (hcoord : ∀ n : N, (d.coordinates n).toAdd=
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf N) n)) :
    ∃ qbar : (H ⧸ Z.subgroupOf H) →* D,
      Function.Surjective qbar ∧ qbar.comp (QuotientGroup.mk' (Z.subgroupOf H))=q ∧
      ∃ e : (N ⧸ Z.subgroupOf N) ≃* qbar.ker,
        (∀ n : N, (e (QuotientGroup.mk' (Z.subgroupOf N) n) : H ⧸ Z.subgroupOf H)=
          QuotientGroup.mk' (Z.subgroupOf H) (inclusion d.section_le n)) ∧
        ∀ (h : H) (v : qbar.ker),
          Additive.ofMul (e.symm (MulAut.conjNormal (QuotientGroup.mk' (Z.subgroupOf H) h) v))=
            ρ (q h) (Additive.ofMul (e.symm v)) := by
  let E := H ⧸ Z.subgroupOf H
  let π : H →* E := QuotientGroup.mk' (Z.subgroupOf H)
  have hmem (h : H) : q h=1 ↔ (h:G)∈N := by
    change h∈q.ker ↔ h∈N.subgroupOf H
    rw [hk]
  have hkill : Z.subgroupOf H≤q.ker := fun h hh => (hmem h).mpr (d.kernel_le hh)
  let qbar : E →* D := QuotientGroup.lift (Z.subgroupOf H) q hkill
  have hbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective _ q hq hkill
  let f : N →* qbar.ker := (π.comp (inclusion d.section_le)).codRestrict qbar.ker
    (fun n => (hmem (inclusion d.section_le n)).mpr n.property)
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨h,hh⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf H) (v:E)
    have hn : (h:G)∈N := (hmem h).mp (by
      change qbar (π h)=1
      rw [hh]
      exact v.property)
    exact ⟨⟨h,hn⟩,Subtype.ext hh⟩
  have hfk : f.ker=Z.subgroupOf N := by
    ext n
    change (⟨π (inclusion d.section_le n),_⟩ : qbar.ker)=1 ↔ (n:G)∈Z
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (N:=Z.subgroupOf H) (inclusion d.section_le n)
  let e : (N ⧸ Z.subgroupOf N) ≃* qbar.ker :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (n : N) : e (QuotientGroup.mk' (Z.subgroupOf N) n)=f n := by
    change (QuotientGroup.quotientKerEquivOfSurjective f hf)
      ((QuotientGroup.quotientMulEquivOfEq hfk.symm) (QuotientGroup.mk n))=f n
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  refine ⟨qbar,hbar,QuotientGroup.lift_comp_mk' _ q hkill,e,?_,?_⟩
  · intro n
    rw [he]
    rfl
  · intro h v
    obtain ⟨n,rfl⟩ := hf v
    let m : N := ⟨(h:G)*n*(h:G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized h.property) n).mp n.property⟩
    have hm : MulAut.conjNormal (π h) (f n)=f m := by
      apply Subtype.ext
      change π h*π (inclusion d.section_le n)*(π h)⁻¹=π (inclusion d.section_le m)
      rw [←map_inv,←map_mul,←map_mul]
      rfl
    rw [hm,←he,←he,e.symm_apply_apply,e.symm_apply_apply]
    have hh := d.equivariant h n
    rw [hcoord,hcoord] at hh
    exact hh

end Representation.BinaryConjugationSection
