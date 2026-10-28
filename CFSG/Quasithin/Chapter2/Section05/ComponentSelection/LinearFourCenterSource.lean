module
public import Theory.SpecificGroups.PSL3Four.CentralCover.NonElementaryParabolic
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MarkSource
/-! # The original exceptional-cover input to the field reduction
A non-elementary center would equal the component Sylow center by I.2.2(3a),
contradicting the source mark's proved noncentral projection there. Thus the
center is elementary. The exact I.2.2(3b) family now applies to the literal
parabolic and solvable residual, including the natural quotient action,
elementary preimages and compatible graph-field lift. No center or module
hypothesis remains beyond the original source setup and actual PSL₃(4) model.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555, using I.2.2(3). -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.linear_four_center_frattini
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L ⧸ center L ≃* Matrix.PSL3Four.PSL) : frattini (center L)=⊥ := by
  let h := c.localSetup hG structural115Input sourceC
  let := h.quasisimple
  have hZ : IsPGroup 2 (center L) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  by_contra hphi
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) c.component.1
  let f : L.subgroupOf H ≃* L := subgroupOfEquivOfLe c.component_le
  let P : Sylow 2 L := R.mapSurjective (f:=f.toMonoidHom) f.surjective
  have hP : (P:Subgroup L)=((S:Subgroup H).map H.subtype).subgroupOf L := by
    ext l
    constructor
    · rintro ⟨r,hr,rfl⟩
      have hh : r∈(S:Subgroup H).subgroupOf (L.subgroupOf H) := hR ▸ hr
      exact mem_map_of_mem H.subtype hh
    · rintro ⟨a,ha,hea⟩
      refine ⟨f.symm l,?_,f.apply_symm_apply l⟩
      rw [hR]
      change (⟨l,c.component_le l.property⟩:H)∈S
      have he : (⟨l,c.component_le l.property⟩:H)=a := Subtype.ext hea.symm
      rwa [he]
  obtain ⟨t,ht,htZ,_,_⟩ := MathieuSourceSetup.central_sylow_projection c hG sourceC hempty
  have hc := (Matrix.PSL3Four.NonElementaryKernel.source_nonElementary_center e hZ hphi P).1
  apply htZ
  apply hc.le
  have htP : (t:L)∈(P:Subgroup L) := by rw [hP]; exact t.property
  refine ⟨⟨t,htP⟩,?_,rfl⟩
  change (⟨t,htP⟩:(P:Subgroup L))∈center (P:Subgroup L)
  rw [mem_center_iff]
  intro u
  exact Subtype.ext (congrArg (fun v:((S:Subgroup H).map H.subtype).subgroupOf L=>(v:L))
    (mem_center_iff.mp ht ⟨u,by rw [←hP]; exact u.property⟩))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
