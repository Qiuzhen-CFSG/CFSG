module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InnerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.OrbitSource
public import Theory.GroupTheory.MarkedInnerStrongClosure.ReturningConjugates
/-! # The literal central mark in the component-generated source group
The original inner action has an implementer in the actual component Sylow,
central in that Sylow and noncentral in the component. Its remaining factor
lies in the prescribed Sylow centralizer. Consequently z lies outside the
actual two-core, and in the normal-component branch z belongs to K O₂(H).
No involutory lift through the component center is asserted.
Source: Aschbacher--Smith, Notation 2.5.4 and proof of 2.5.7, printed p.554. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
theorem MathieuSourceSetup.sylow_projection
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅) :
    ∃ t : L, t∈((S:Subgroup H).map H.subtype).subgroupOf L ∧ t∉center L ∧
      (∀ x:L, ((t*x*t⁻¹:L):G)=z*(x:G)*z⁻¹) ∧
      ((t:G)⁻¹*z)∈(S:Subgroup H).map H.subtype ⊓ centralizer (L:Set G) := by
  let h := c.localSetup hG structural115Input sourceC
  obtain ⟨α,hα,⟨t,ht⟩⟩ := MathieuSourceSetup.inner_action c hG sourceC hempty
  have ha (x:L) : ((t*x*t⁻¹:L):G)=z*(x:G)*z⁻¹ := by
    have he : (MulAut.conj t) x = α x := DFunLike.congr_fun ht x
    exact (congrArg Subtype.val he).trans (hα x)
  have htZ : t∉center L := by
    intro hz
    apply h.action_ne_one α hα
    rw [← ht]
    apply MulEquiv.ext
    intro x
    change t*x*t⁻¹=x
    rw [← mem_center_iff.mp hz x]
    exact mul_inv_cancel_right x t
  let q := QuotientGroup.mk' (center L)
  have hqt : q t≠1 := fun he => htZ ((QuotientGroup.eq_one_iff _).mp he)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) c.component.1
  let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe c.component_le
  let P : Sylow 2 L := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hPS : (P:Subgroup L).map L.subtype ≤ (S:Subgroup H).map H.subtype := by
    rintro _ ⟨l,hl,rfl⟩
    obtain ⟨r,hr,her⟩ := hl
    rw [← her]
    have hh : r ∈ (S:Subgroup H).subgroupOf (L.subgroupOf H) := hR ▸ hr
    exact mem_map_of_mem H.subtype hh
  have hker : q.ker=center L := QuotientGroup.ker_mk' _
  have hkp : IsPGroup 2 q.ker := by
    rw [hker,MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  obtain ⟨htP,_,_⟩ := MarkedInnerStrongClosure.central_two_quotient_marker
    ((S:Subgroup H).map H.subtype) L.subtype L.subtype_injective P hPS q
    (QuotientGroup.mk'_surjective _) hker hkp z
    (h.involution ▸ pow_orderOf_eq_one z) (fun a ha=> (h.central a ha).symm) t hqt ha
  have htS := hPS (mem_map_of_mem L.subtype htP)
  refine ⟨t,htS,htZ,ha,?_,?_⟩
  · exact ((S:Subgroup H).map H.subtype).mul_mem
      (((S:Subgroup H).map H.subtype).inv_mem htS) h.mem_sylow
  · intro x hx
    have he : ((t:G)⁻¹*z)*x*((t:G)⁻¹*z)⁻¹=x := by
      calc
        _ = (t:G)⁻¹*(z*x*z⁻¹)*t := by group
        _ = x := by rw [← ha ⟨x,hx⟩]; change (t:G)⁻¹*((t:G)*x*(t:G)⁻¹)*t=x; group
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The nonzero projection is central in the actual component Sylow. -/
theorem MathieuSourceSetup.central_sylow_projection
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅) :
    ∃ t : ((S:Subgroup H).map H.subtype).subgroupOf L,
      t∈center (((S:Subgroup H).map H.subtype).subgroupOf L) ∧
      (t:L)∉center L ∧
      (∀ x:L, (((t:L)*x*(t:L)⁻¹:L):G)=z*(x:G)*z⁻¹) ∧
      (((t:L):G)⁻¹*z)∈(S:Subgroup H).map H.subtype ⊓ centralizer (L:Set G) := by
  obtain ⟨t,ht,htZ,ha,hc⟩ := MathieuSourceSetup.sylow_projection c hG sourceC hempty
  refine ⟨⟨t,ht⟩,?_,htZ,ha,hc⟩
  rw [mem_center_iff]
  intro x
  apply Subtype.ext
  apply Subtype.ext
  have h := c.localSetup hG structural115Input sourceC
  have he : (t:G)*(x:L)*(t:G)⁻¹=(x:L) := by
    change ((t*(x:L)*t⁻¹:L):G)=(x:L)
    rw [ha (x:L),← (h.central (x:L) x.property)]
    exact mul_inv_cancel_right ((x:L):G) z
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The source mark is outside the literal core, without component normality. -/
theorem MathieuSourceSetup.mark_not_mem_twoCore
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=L⊔(S:Subgroup H).map H.subtype) : z∉twoCore H := by
  obtain ⟨t,ht,htZ,ha,hc⟩ := MathieuSourceSetup.sylow_projection c hG sourceC hempty
  intro hz
  rw [← generated_orbit_core ⟨c.component_le,c.component⟩ S hgen] at hz
  apply htZ
  rw [mem_center_iff]
  intro x
  apply Subtype.ext
  have hx : (x:G)∈componentOrbit L ((S:Subgroup H).map H.subtype) :=
    le_componentOrbit _ _ x.property
  have he : (t:G)*(x:G)*(t:G)⁻¹=(x:G) := by
    change ((t*x*t⁻¹:L):G)=(x:G)
    rw [ha x,← hz.2 x hx]
    exact mul_inv_cancel_right (x:G) z
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Original 2.5.4 in its normal-component branch: the same z lies in
K O₂(H), with a noncentral component projection. -/
theorem MathieuSourceSetup.mark_mem_component_sup_twoCore
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=L⊔(S:Subgroup H).map H.subtype)
    (hn : (L.subgroupOf H).Normal) :
    z∈L⊔twoCore H ∧ z∉twoCore H := by
  have hSL : (S:Subgroup H).map H.subtype≤normalizer (L:Set G) :=
    (map_subtype_le _).trans ((normal_subgroupOf_iff_le_normalizer c.component_le).mp hn)
  have ho : componentOrbit L ((S:Subgroup H).map H.subtype)=L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hSL)
      (le_componentOrbit _ _)
  have he := generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
  rw [ho] at he
  obtain ⟨t,ht,htZ,ha,hc⟩ := MathieuSourceSetup.sylow_projection c hG sourceC hempty
  refine ⟨?_,MathieuSourceSetup.mark_not_mem_twoCore c hG sourceC hempty hgen⟩
  have hcQ : (t:G)⁻¹*z∈twoCore H := he ▸ hc
  have hm := (L⊔twoCore H).mul_mem ((show L≤L⊔twoCore H from le_sup_left) t.property)
    ((show twoCore H≤L⊔twoCore H from le_sup_right) hcQ)
  simpa only [mul_inv_cancel_left] using hm
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
