module
public import Theory.SpecificGroups.DihedralProduct.FactorGraph
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.SourceCoordinates

/-!
# Marked factor alignment for the terminal source

The finite graph calculation compares any two commuting dihedral factors with
ordered central axes. Failure of source alignment gives a literal conjugate
of z outside B, exactly the witness consumed by weak closure.
Source: Aschbacher--Smith, 13.9.10, printed p.973.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G:Type*} [Group G] {d:Configuration G} (m:Marking d)

private theorem second_axis_center :
    m.baseProductEmbedding (1,DihedralGroup.r 2)=m.t*m.z := by
  rw [←m.baseProductEmbedding_axis,←m.sylowModelEmbedding_center]
  change m.baseProductEmbedding (1,DihedralGroup.r 2)=
    m.baseProductEmbedding (DihedralGroup.r 2,1)*m.baseProductEmbedding (DihedralGroup.r 2,DihedralGroup.r 2)
  rw [←map_mul]
  exact congrArg m.baseProductEmbedding (by decide)

/-- The concrete factor comparison keeps both original central axes. -/
theorem first_factor_central_graph
    (f g:D8→*G) (hf:Function.Injective f)
    (hfJ:f.range≤m.dihedralBase) (hgJ:g.range≤m.dihedralBase)
    (hft:f (DihedralGroup.r 2)=m.t) (hgt:g (DihedralGroup.r 2)=m.t*m.z)
    (hcomm:∀a b,Commute (f a) (g b))
    (x:G) (hx:x∈m.factorSylow 1) : x∈f.range ∨ x*m.z∈f.range := by
  let j : D8×D8 ≃* m.dihedralBase :=
    (MonoidHom.ofInjective m.baseProductEmbedding_injective).trans
      (MulEquiv.subgroupCongr m.range_baseProductEmbedding)
  let fc:=f.codRestrict m.dihedralBase (fun a=>hfJ ⟨a,rfl⟩)
  let gc:=g.codRestrict m.dihedralBase (fun a=>hgJ ⟨a,rfl⟩)
  let ff:=j.symm.toMonoidHom.comp fc
  let gg:=j.symm.toMonoidHom.comp gc
  have hff:Function.Injective ff := by
    intro a b hab
    exact hf (congrArg Subtype.val (j.symm.injective hab))
  have hfft:ff (DihedralGroup.r 2)=(DihedralGroup.r 2,1) := by
    apply j.injective
    change j (j.symm (fc (DihedralGroup.r 2)))=_
    rw [j.apply_symm_apply]
    apply Subtype.ext
    exact hft.trans m.baseProductEmbedding_axis.symm
  have hggt:gg (DihedralGroup.r 2)=(1,DihedralGroup.r 2) := by
    apply j.injective
    change j (j.symm (gc (DihedralGroup.r 2)))=_
    rw [j.apply_symm_apply]
    apply Subtype.ext
    exact hgt.trans m.second_axis_center.symm
  have hfg:∀a b,Commute (ff a) (gg b) := by
    intro a b
    exact (show Commute (fc a) (gc b) from Subtype.ext (hcomm a b).eq).map j.symm.toMonoidHom
  have hxJ:=m.factorSylow_le_dihedralBase 1 hx
  rw [←m.range_baseProductEmbedding] at hxJ
  obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
  have hb: b=1:=(m.baseProductEmbedding_mem_first a b).mp hx
  subst b
  obtain ⟨c,hc⟩:=DihedralProduct.first_axis_lift ff gg hff hfft hggt hfg a
  have hfimage (v:D8×D8) (hh:ff c=v) : f c=m.baseProductEmbedding v := by
    have he:=congrArg j hh
    change j (j.symm (fc c))=j v at he
    rw [j.apply_symm_apply] at he
    exact congrArg Subtype.val he
  rcases hc with hc|hc
  · exact Or.inl ⟨c,hfimage _ hc⟩
  · right
    refine ⟨c*DihedralGroup.r 2,?_⟩
    rw [map_mul,hfimage _ hc,hft,←m.baseProductEmbedding_axis,←map_mul,
      ←m.sylowModelEmbedding_center]
    change m.baseProductEmbedding ((a,DihedralGroup.r 2)*(DihedralGroup.r 2,1))=
      m.baseProductEmbedding (a,1)*m.baseProductEmbedding (DihedralGroup.r 2,DihedralGroup.r 2)
    rw [←map_mul]
    apply congrArg m.baseProductEmbedding
    simp

/-- Failure of E-alignment constructs the original conjugate of z in R1\B. -/
theorem exists_alignment_conjugate
    (f g:D8→*G) (hf:Function.Injective f)
    (hfJ:f.range≤m.dihedralBase) (hgJ:g.range≤m.dihedralBase)
    (hft:f (DihedralGroup.r 2)=m.t) (hgt:g (DihedralGroup.r 2)=m.t*m.z)
    (hcomm:∀a b,Commute (f a) (g b)) (hE:¬m.terminalFour≤f.range) :
    ∃a:G,a*m.z*a⁻¹∈f.range ∧ a*m.z*a⁻¹∉m.B := by
  classical
  obtain ⟨e,he,heR⟩:=SetLike.not_le_iff_exists.mp hE
  have heT:m.terminalFour≤m.factorSylow 1 := by rw [m.terminalFour_eq_source];exact inf_le_left
  have herz : e*m.z∈f.range :=
    (m.first_factor_central_graph f g hf hfJ hgJ hft hgt hcomm e (heT he)).resolve_left heR
  have heB:e∉m.B := by
    intro heB
    have htR:m.t∈f.range:=⟨DihedralGroup.r 2,hft⟩
    exact heR ((zpowers_le.mpr htR) (m.terminalFour_inf_B ▸ (show e∈m.terminalFour⊓m.B from ⟨he,heB⟩)))
  obtain ⟨hc,hn⟩:=m.terminalFour_mul_z_conjugate e he heB
  obtain ⟨a,ha⟩:=isConj_iff.mp hc
  exact ⟨a,ha.symm ▸ herz,ha.symm ▸ hn⟩
end CFSG.Quasithin.Chapter13.Section09.Marking
