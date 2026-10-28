module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.SylowDihedralKernel
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The dihedral Sylow kernel retains its full native centralizer marking

The transport uses one ambient conjugation. Consequently the centralizer
of the kernel center normalizes the kernel, in the whole native group.
This additional ambient clause is needed when the original local group is
embedded in the native sextet stabilizer; a bare abstract kernel isomorphism
does not supply it.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

private theorem marked_mem_kernel_embedded_center :
    involution2A∈(center (kernel.map centralizer2A.subtype)).map
      (kernel.map centralizer2A.subtype).subtype := by
  let P₀ := kernel.map centralizer2A.subtype
  let m : centralizer2A := ⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩
  have hmZ : m∈center centralizer2A := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  have hmK : m∈kernel := kernel_selfCentralizing (center_le_centralizer _ hmZ)
  have hmk : (⟨m,hmK⟩:kernel)∈center kernel := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (mem_center_iff.mp hmZ k.val)
  have hh : (m:M24)∈(center P₀).map P₀.subtype := by
    rw [show P₀=kernel.map centralizer2A.subtype from rfl,
      ←map_embeddedCenter kernel centralizer2A.subtype centralizer2A.subtype_injective]
    exact ⟨m,⟨(⟨m,hmK⟩:kernel),hmk,rfl⟩,rfl⟩
  exact hh

public theorem exists_sylow_dihedral_kernel_marked (S : Sylow 2 M24) :
    ∃ π : S→*DihedralGroup 4, Function.Surjective π ∧
      centralizer (π.ker : Set S)≤π.ker ∧ Nonempty (π.ker≃*kernel) ∧
      let P := π.ker.map (S : Subgroup M24).subtype
      centralizer ((center P).map P.subtype : Set M24)≤normalizer (P : Set M24) := by
  let R : Sylow 2 centralizer2A := Classical.choice inferInstance
  let q : centralizer2A→*Matrix.PSL3Two.PSL :=
    quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' kernel)
  have hq : Function.Surjective q := quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective kernel)
  have hk : q.ker=kernel := by
    rw [MonoidHom.ker_comp_of_injective _ _ quotientEquiv.injective,QuotientGroup.ker_mk']
  obtain ⟨d⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral
    (R.mapSurjective hq)
  let r : R→*R.mapSurjective hq := q.subgroupMap (R : Subgroup centralizer2A)
  let ψ := d.toMonoidHom.comp r
  have hψ : Function.Surjective ψ := d.surjective.comp (q.subgroupMap_surjective _)
  have hψker : ψ.ker=kernel.subgroupOf R := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective]
    change (q.subgroupMap (R : Subgroup centralizer2A)).ker=_
    rw [Subgroup.ker_subgroupMap,hk]
  have hKR : kernel≤(R : Subgroup centralizer2A) := kernel_isTwoGroup.le_sylow_of_normal R
  let P₀ := kernel.map centralizer2A.subtype
  let R₀ := (R : Subgroup centralizer2A).map centralizer2A.subtype
  have hRc : Nat.card R₀=1024 := by
    rw [card_map_of_injective centralizer2A.subtype_injective,R.card_eq_multiplicity,centralizer_card]
    decide +kernel
  let S₀ : Sylow 2 M24 := Sylow.ofCard R₀ (by rw [hRc,m24_order]; decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S₀ S
  let c := MulAut.conj g
  have hRS : (S₀ : Subgroup M24).map c.toMonoidHom=(S : Subgroup M24) :=
    congrArg Sylow.toSubgroup hg
  let e₀ : R≃*S₀ := (R : Subgroup centralizer2A).equivMapOfInjective
    centralizer2A.subtype centralizer2A.subtype_injective
  let ec : S₀≃*S := ((S₀ : Subgroup M24).equivMapOfInjective c.toMonoidHom c.injective).trans
    (MulEquiv.subgroupCongr hRS)
  let e : R≃*S := e₀.trans ec
  have he (x : R) : (e x : M24)=c x.val.val := rfl
  let π := ψ.comp e.symm.toMonoidHom
  have hmap : π.ker.map (S : Subgroup M24).subtype=P₀.map c.toMonoidHom := by
    apply le_antisymm
    · rintro x ⟨s,hs,rfl⟩
      have hr : e.symm s∈ψ.ker := hs
      rw [hψker] at hr
      have hx : c (e.symm s).val.val=(s:M24) := by
        rw [←he,e.apply_symm_apply]
      exact mem_map.mpr ⟨(e.symm s).val.val,mem_map_of_mem _ hr,hx⟩
    · rintro x ⟨_,⟨k,hk,rfl⟩,rfl⟩
      let v : R := ⟨k,hKR hk⟩
      refine ⟨e v,?_,he v⟩
      change ψ (e.symm (e v))=1
      rw [e.symm_apply_apply]
      exact (show v∈ψ.ker from hψker.symm ▸ hk)
  let eker : π.ker≃*ψ.ker := {
    toFun x := ⟨e.symm x.val,x.property⟩
    invFun y := ⟨e y.val,by change ψ (e.symm (e y.val))=1; rw [e.symm_apply_apply]; exact y.property⟩
    left_inv x := Subtype.ext (e.apply_symm_apply x.val)
    right_inv y := Subtype.ext (e.symm_apply_apply y.val)
    map_mul' x y := Subtype.ext (e.symm.map_mul x.val y.val) }
  refine ⟨π,hψ.comp e.symm.surjective,?_,
    ⟨eker.trans ((MulEquiv.subgroupCongr hψker).trans (subgroupOfEquivOfLe hKR))⟩,?_⟩
  · intro x hx
    have hc : e.symm x∈centralizer (ψ.ker : Set R) := by
      intro y hy
      have hh := congrArg e.symm (hx (e y) (by
        change ψ (e.symm (e y))=1
        rw [e.symm_apply_apply]
        exact hy))
      simpa only [map_mul,e.symm_apply_apply] using hh
    have hm : e.symm x∈kernel.subgroupOf R := by
      apply kernel_selfCentralizing
      intro k hk
      exact congrArg Subtype.val (hc (⟨k,hKR hk⟩:R) (hψker.symm ▸ hk))
    change e.symm x∈ψ.ker
    exact hψker.symm ▸ hm
  · let P := π.ker.map (S : Subgroup M24).subtype
    have hmPc : c involution2A∈(center P).map P.subtype := by
      rw [show P=P₀.map c.toMonoidHom from hmap,←map_embeddedCenter P₀ c.toMonoidHom c.injective]
      exact mem_map_of_mem _ marked_mem_kernel_embedded_center
    have hNP : centralizer2A≤normalizer (P₀ : Set M24) := by
      intro x hx
      exact kernel.le_normalizer_map centralizer2A.subtype
        (mem_map_of_mem _ (show (⟨x,hx⟩:centralizer2A)∈normalizer (kernel : Set centralizer2A) by
          rw [normalizer_eq_top]; exact mem_top _))
    change centralizer ((center P).map P.subtype : Set M24)≤normalizer (P : Set M24)
    intro x hx
    have hc : c.symm x∈centralizer2A := by
      apply mem_centralizer_singleton_iff.mpr
      apply c.injective
      simpa only [map_mul,c.apply_symm_apply] using (hx (c involution2A) hmPc).symm
    have hn := (map_mono hNP).trans (P₀.le_normalizer_map c.toMonoidHom)
      (mem_map_of_mem c.toMonoidHom hc)
    change c (c.symm x)∈normalizer (P₀.map c.toMonoidHom : Set M24) at hn
    rw [c.apply_symm_apply,←hmap] at hn
    exact hn

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
