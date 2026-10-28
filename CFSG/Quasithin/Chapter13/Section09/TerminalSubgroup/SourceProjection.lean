module
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.SourceSylow

/-!
# The actual terminal Sylow as a central graph

The intersection J(T)∩H injects into the second dihedral coordinate: its kernel
lies in E∩H, already killed by central transfer. Its order is therefore at most
eight. Any generated order-eight subgroup in this intersection identifies the
literal Sylow of H, with a genuine D8 equivalence, even if it is a central graph
rather than the original second factor. The source pair-centralizer theorem
identifies the entire centralizer in H of tz with the same intersection.
Source: Aschbacher--Smith, proof of 13.9.1, pp.973--974.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath TerminalSubgroup
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

def terminalBaseProjection : (m.dihedralBase⊓terminal m.terminalFour:Subgroup G)→*D8 :=
  let j : D8×D8≃*m.dihedralBase :=
    (MonoidHom.ofInjective m.baseProductEmbedding_injective).trans
      (MulEquiv.subgroupCongr m.range_baseProductEmbedding)
  (MonoidHom.snd D8 D8).comp (j.symm.toMonoidHom.comp (inclusion inf_le_left))

theorem terminalBaseProjection_injective : Function.Injective m.terminalBaseProjection := by
  apply m.terminalBaseProjection.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxJ:=x.property.1
  have hxrange : (x:G)∈m.baseProductEmbedding.range := by
    exact Eq.mp (congrArg (fun S:Subgroup G=>(x:G)∈S) m.range_baseProductEmbedding.symm) hxJ
  obtain ⟨⟨a,b⟩,he⟩:=hxrange
  have hb:b=1 := by
    have hproj:m.terminalBaseProjection x=b := by
      change ((MonoidHom.ofInjective m.baseProductEmbedding_injective).symm
        ((MulEquiv.subgroupCongr m.range_baseProductEmbedding).symm (inclusion inf_le_left x))).2=b
      have hh : ((MulEquiv.subgroupCongr m.range_baseProductEmbedding).symm (inclusion inf_le_left x))=
        MonoidHom.ofInjective m.baseProductEmbedding_injective (a,b) := Subtype.ext he.symm
      rw [hh,MulEquiv.symm_apply_apply]
    exact hproj.symm.trans hx
  subst b
  have hxC:(x:G)∈centralizer (m.terminalFour:Set G) := residual_le _ x.property.2
  have ha:a∈plane true := (m.base_centralizer_terminalFour a 1).mp (he.symm ▸ hxC)
  have hxE:(x:G)∈m.terminalFour := he ▸ (m.terminalFour_coordinate a 1).mpr ⟨ha,rfl⟩
  exact Subtype.ext (disjoint_def.mp m.terminalFour_disjoint_terminal hxE x.property.2)

theorem terminalBase_card_le : Nat.card (m.dihedralBase⊓terminal m.terminalFour:Subgroup G)≤8 := by
  have hh:=Nat.card_le_card_of_injective m.terminalBaseProjection m.terminalBaseProjection_injective
  simpa only [DihedralGroup.nat_card] using hh

/-- Any order-eight subgroup generated inside the original terminal base is
exactly its intersection with H, allowing central graphs of T₂. -/
theorem terminalBase_eq_of_eight (D:Subgroup G) (hDJ:D≤m.dihedralBase)
    (hDH:D≤terminal m.terminalFour) (hcard:Nat.card D=8) :
    m.dihedralBase⊓terminal m.terminalFour=D := by
  apply (eq_of_le_of_card_ge (le_inf hDJ hDH) ?_).symm
  rw [hcard]
  exact m.terminalBase_card_le

/-- The actual generated terminal Sylow has the dihedral model, independently
of whether its first coordinate is a nontrivial central graph. -/
def terminalBaseDihedralEquiv (D:Subgroup G) (hDJ:D≤m.dihedralBase)
    (hDH:D≤terminal m.terminalFour) (hcard:Nat.card D=8) : D≃*D8 :=
  (MulEquiv.subgroupCongr (m.terminalBase_eq_of_eight D hDJ hDH hcard).symm).trans
    (MulEquiv.ofBijective m.terminalBaseProjection ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨m.terminalBaseProjection_injective,by
        rw [m.terminalBase_eq_of_eight D hDJ hDH hcard,hcard,DihedralGroup.nat_card]⟩))

/-- The intersection with the original dihedral base is intrinsically Sylow
in the actual terminal residual. -/
theorem exists_terminalBase_sylow :
    ∃P:Sylow 2 (terminal m.terminalFour),
      (P:Subgroup (terminal m.terminalFour)).map (terminal m.terminalFour).subtype=
        m.dihedralBase⊓terminal m.terminalFour := by
  let C:=centralizer (m.terminalFour:Set G)
  let R:=pResidual 2 C
  obtain ⟨S,hS⟩:=m.exists_terminalFour_centralizer_sylow
  obtain ⟨P,hP⟩:=S.exists_sylow_map_eq_inf_of_normal R
  let e:R≃*terminal m.terminalFour:=R.equivMapOfInjective C.subtype C.subtype_injective
  refine ⟨P.mapSurjective (f:=e.toMonoidHom) e.surjective,?_⟩
  change ((P:Subgroup R).map e.toMonoidHom).map (terminal m.terminalFour).subtype=_
  calc
    _ = ((P:Subgroup R).map R.subtype).map C.subtype := by
      rw [map_map,map_map];rfl
    _ = ((S:Subgroup C)⊓R).map C.subtype := by rw [hP]
    _ = ((S:Subgroup C).map C.subtype)⊓terminal m.terminalFour :=
      map_inf _ _ _ C.subtype_injective
    _ = (m.terminalFour⊔m.factorSylow turn)⊓terminal m.terminalFour := by rw [hS]
    _ = m.dihedralBase⊓terminal m.terminalFour := by
      rw [←m.base_inf_centralizer_terminalFour,inf_assoc,inf_eq_right.mpr (residual_le C)]

/-- Recognition uses the central involution tz in the actual H, with its
whole ambient centralizer identified by the source pair-centralizer theorem. -/
theorem terminal_centralizer_eq_base (hE:IsEvenCharacteristicAt d.T)
    (hmem:m.t*m.z∈terminal m.terminalFour) :
    (centralizer ({(⟨m.t*m.z,hmem⟩:terminal m.terminalFour)}:Set (terminal m.terminalFour))).map
      (terminal m.terminalFour).subtype=m.dihedralBase⊓terminal m.terminalFour := by
  rw [map_subtype_centralizer_singleton]
  apply le_antisymm
  · rintro x ⟨hxH,hxC⟩
    have hxE:x∈centralizer (m.terminalFour:Set G):=residual_le _ hxH
    have hxt:x*m.t=m.t*x:=
      (mem_centralizer_iff.mp hxE m.t m.t_mem_terminalFour).symm
    have hxz:x*m.z=m.z*x := by
      have ht:=mem_centralizer_singleton_iff.mp hxC
      change x*(m.t*m.z)=(m.t*m.z)*x at ht
      calc
        x*m.z = m.t⁻¹*(m.t*x)*m.z := by group
        _ = m.t⁻¹*(x*m.t)*m.z := by rw [hxt]
        _ = m.z*x := by rw [mul_assoc,mul_assoc,ht];group
    have hxJ:x∈m.dihedralBase := by
      rw [←m.elementary_thompson,←m.marked_common_centralizer hE]
      exact ⟨mem_centralizer_singleton_iff.mpr hxz,mem_centralizer_singleton_iff.mpr hxt⟩
    exact ⟨hxJ,hxH⟩
  · rintro x ⟨hxJ,hxH⟩
    refine ⟨hxH,mem_centralizer_singleton_iff.mpr ?_⟩
    have hxt: x*m.t=m.t*x:=
      (mem_centralizer_iff.mp (residual_le _ hxH) m.t m.t_mem_terminalFour).symm
    have hxT:x∈(d.T:Subgroup G) := by
      rw [←m.range_baseProductEmbedding] at hxJ
      obtain ⟨⟨a,b⟩,rfl⟩:=hxJ
      exact m.baseProductEmbedding_mem_sylow a b
    have hxz:x*m.z=m.z*x:=mem_centralizer_singleton_iff.mp (m.z_central_sylow hxT)
    change x*(m.t*m.z)=(m.t*m.z)*x
    rw [←mul_assoc,hxt,mul_assoc,hxz,mul_assoc]

end CFSG.Quasithin.Chapter13.Section09.Marking
