module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelComparison
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Uniqueness of the native extraspecial kernel with its original center

The marked center places the actual candidate in the full involution
centralizer. The natural/dual section comparison identifies that candidate
with the intrinsic two-core. In particular the full centralizer normalizes
the original candidate; no choice of a replacement extraspecial subgroup is
made and no normality in a Sylow subgroup is assumed.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

/-- The embedded center and order determine the actual extraspecial subgroup. -/
theorem extraspecial_eq_embedded_kernel (P : Subgroup M24) [IsExtraspecial 2 P]
    (hcard : Nat.card P=128)
    (hcenter : (center P).map P.subtype=zpowers involution2A) :
    P=kernel.map centralizer2A.subtype := by
  have hPC : P≤centralizer2A := by
    have hm : involution2A∈(center P).map P.subtype := by
      rw [hcenter]
      exact mem_zpowers _
    obtain ⟨m,hm,he⟩ := hm
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (mem_center_iff.mp hm ⟨x,hx⟩)
    change x * (m : M24) = (m : M24) * x at hh
    change (m : M24)=involution2A at he
    rw [he] at hh
    exact hh
  let Q := P.subgroupOf centralizer2A
  let e : Q≃*P := subgroupOfEquivOfLe hPC
  let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv e.symm inferInstance
  have hQcard : Nat.card Q=128 := (Nat.card_congr e.toEquiv).trans hcard
  have hQcenter : (center Q).map Q.subtype=zpowers
      (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A) := by
    apply map_injective centralizer2A.subtype_injective
    rw [map_embeddedCenter Q centralizer2A.subtype centralizer2A.subtype_injective,
      show Q.map centralizer2A.subtype=P from map_subgroupOf_eq_of_le hPC,
      hcenter,MonoidHom.map_zpowers]
    rfl
  have heq := KernelComparison.extraspecial_eq_kernel Q hQcard hQcenter
  have hh := congrArg (Subgroup.map centralizer2A.subtype) heq
  simpa only [show Q=P.subgroupOf centralizer2A from rfl,map_subgroupOf_eq_of_le hPC] using hh

/-- The full centralizer normalizes the very same extraspecial candidate. -/
theorem centralizer_le_normalizer_of_extraspecial_marking
    (P : Subgroup M24) [IsExtraspecial 2 P]
    (hcard : Nat.card P=128)
    (hcenter : (center P).map P.subtype=zpowers involution2A) :
    centralizer2A≤normalizer (P : Set M24) := by
  rw [extraspecial_eq_embedded_kernel P hcard hcenter]
  intro x hx
  apply kernel.le_normalizer_map centralizer2A.subtype
  exact mem_map_of_mem _ (show (⟨x,hx⟩ : centralizer2A)∈normalizer
    (kernel : Set centralizer2A) from le_normalizer_of_normal (mem_top _))

/-- The comparison is invariant under one simultaneous ambient conjugation
of the original candidate and its marked central involution. -/
theorem centralizer_le_normalizer_of_conjugate_extraspecial_marking
    (P : Subgroup M24) [IsExtraspecial 2 P]
    (hcard : Nat.card P=128) (z : M24) (hz : IsConj involution2A z)
    (hcenter : (center P).map P.subtype=zpowers z) :
    centralizer ({z} : Set M24)≤normalizer (P : Set M24) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hz.symm
  let c := MulAut.conj g
  have hcz : c z=involution2A := hg
  let Q := P.map c.toMonoidHom
  let e : P≃*Q := P.equivMapOfInjective c.toMonoidHom c.injective
  let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv e inferInstance
  have hQcard : Nat.card Q=128 := (Nat.card_congr e.symm.toEquiv).trans hcard
  have hQcenter : (center Q).map Q.subtype=zpowers involution2A := by
    rw [show Q=P.map c.toMonoidHom from rfl,
      ←map_embeddedCenter P c.toMonoidHom c.injective,hcenter,MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,hcz]
  have hn := centralizer_le_normalizer_of_extraspecial_marking Q hQcard hQcenter
  intro x hx
  have hcx : c x∈centralizer2A := by
    apply mem_centralizer_singleton_iff.mpr
    rw [←hcz,←map_mul,←map_mul]
    exact congrArg c (mem_centralizer_singleton_iff.mp hx)
  have hh := Q.le_normalizer_map c.symm.toMonoidHom (mem_map_of_mem _ (hn hcx))
  have heq : Q.map c.symm.toMonoidHom=P := by
    rw [show Q=P.map c.toMonoidHom from rfl,map_map]
    have hid : c.symm.toMonoidHom.comp c.toMonoidHom=MonoidHom.id M24 := by
      apply MonoidHom.ext
      intro y
      exact c.symm_apply_apply y
    rw [hid,map_id]
  change c.symm (c x)∈normalizer (Q.map c.symm.toMonoidHom : Set M24) at hh
  rwa [heq,c.symm_apply_apply] at hh

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
