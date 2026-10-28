module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.PlaneClosure
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Ordinary
public import Theory.GroupTheory.PResidual.SimpleQuotientNormalGeneration

/-!
# The original parabolic conjugate generation of L

The invariant natural pairing identifies the seed normalizer in L with
the point normalizer. The literal A₆ quotient makes this a maximal
subgroup. The plane residual does not normalize the point, so its span
under the seed parabolic has normalizer equal to L. Simplicity of the
quotient and two-perfection lift normal generation to L itself.

This proves the literal generation premise used by the ambient seed
centralizer argument, without a block decomposition or plane fusion.
Source: Aschbacher--Smith,13.3.15(6), printed p.894, applied in13.5.4(4),p.916.
-/

@[expose] public section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Ordinary
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem normalizer_preimage (A:Subgroup G) (hA:A≤V) :
    (flagStabilizer (image d A)).comap (localMap d)=(normalizer (A:Set G)).subgroupOf L := by
  ext l
  constructor
  · intro hl
    have hh:=normalizes_plane_of_localMap_stabilizes d
      ((flagStabilizer (image d A)).comap (localMap d)) A hA (map_comap_le _ _)
    exact hh (mem_map_of_mem L.subtype hl)
  · intro hl
    apply (mem_stabilizer_iff_map _ _).mpr
    have hh:=QuadraticSource.image_conjugate_by_local d A hA (inclusion (QuadraticSource.L_le_local d) l)
    rw [←localMap_eq_full d l] at hh
    have he:A.map (MulAut.conj l.val).toMonoidHom=A:=mem_normalizer_iff_map_conj_eq.mp hl
    change image d (A.map (MulAut.conj l.val).toMonoidHom)=_ at hh
    rw [he] at hh
    exact hh.symm

private theorem seed_point_normalizers :
    (normalizer (V₃:Set G)).subgroupOf L=(normalizer (V₁:Set G)).subgroupOf L := by
  rw [←normalizer_preimage d V₃ d.seed_le,←normalizer_preimage d V₁
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))]
  congr 1
  rw [seed_perpendicular d]
  apply le_antisymm _ (stabilizer_le_orthogonal_stabilizer _)
  have hh:=stabilizer_le_orthogonal_stabilizer (form.orthogonal (image d V₁))
  rwa [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] at hh

private theorem point_normalizer_maximal : IsCoatom ((normalizer (V₁:Set G)).subgroupOf L) := by
  obtain ⟨a,ha,_⟩:=QuadraticSource.source_even_flag d
  let b:alternatingGroup (Fin 6):=a*⟨flagRelabel,flagRelabel_even⟩
  let q:L→*alternatingGroup (Fin 6):=d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  let α:L→*alternatingGroup (Fin 6):=(MulAut.conj b⁻¹).toMonoidHom.comp q
  have hα:Function.Surjective α:=(MulAut.conj b⁻¹).surjective.comp
    (d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _))
  have hmark:duadStabilizer.map (MulAut.conj b.val).toMonoidHom=flagStabilizer (image d V₁):=by
    rw [ha,flagStabilizer_move,flagStabilizer_line,←flagRelabel_duad,map_map]
    congr 1
  have he:(normalizer (V₁:Set G)).subgroupOf L=a6DuadStabilizer.comap α:=by
    rw [←normalizer_preimage d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))]
    ext l
    change localMap d l∈flagStabilizer (image d V₁) ↔ α l∈a6DuadStabilizer
    rw [←hmark,mem_map_equiv]
    rfl
  rw [he]
  exact isCoatom_comap_of_surjective hα a6DuadStabilizer_isCoatom

/-- The actual plane residual generates L under conjugation by the original
seed parabolic. Only the ordinary quotient, not a block decomposition, is used. -/
theorem source_parabolic_generation (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6)) :
    L=conjugateSpanBy (planeActor (L:=L) (V₂:=V₂)) (L⊓normalizer (V₃:Set G)) := by
  let X:=planeActor (L:=L) (V₂:=V₂)
  let P:Subgroup L:=(normalizer (V₃:Set G)).subgroupOf L
  let Y:Subgroup L:=X.subgroupOf L
  let K:=conjugateSpanBy Y P
  have hXL:X≤L:=planeActor_le.trans inf_le_left
  have hP:IsCoatom P:=by rw [show P=(normalizer (V₁:Set G)).subgroupOf L from seed_point_normalizers d];exact point_normalizer_maximal d
  have hnY:¬Y≤P:=by
    intro h
    apply planeActor_not_normalizes_line d
    intro x hx
    have hh:=h (show (⟨x,hXL hx⟩:L)∈Y from hx)
    rw [show P=(normalizer (V₁:Set G)).subgroupOf L from seed_point_normalizers d] at hh
    exact hh
  have hnK:¬K≤P:=fun h=>hnY ((le_conjugateSpanBy Y P).trans h)
  have hNP:normalizer (K:Set L)=⊤:=by
    apply hP.2
    exact lt_of_le_of_ne (le_normalizer_conjugateSpanBy Y P) (fun he=>
      hnK (K.le_normalizer.trans_eq he.symm))
  let : K.Normal:=normalizer_eq_top_iff.mp hNP
  let q:L→*alternatingGroup (Fin 6):=d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  have hq:Function.Surjective q:=d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker:q.ker=(localMap d).ker:=by
    ext l
    change q l=1 ↔ (q l).val=1
    exact Subtype.ext_iff
  have hk:IsPGroup 2 q.ker:=by rw [hker,local_kernel_eq_core d e];exact pCore_isPGroup
  have hkp:q.ker≤P:=by
    rw [show P=(normalizer (V₁:Set G)).subgroupOf L from seed_point_normalizers d,
      ←normalizer_preimage d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)),hker]
    exact Subgroup.ker_le_comap _ _
  have hY:Y.map q≠⊥:=fun hz=>hnY (((map_eq_bot_iff Y).mp hz).trans hkp)
  let : IsSimpleGroup (alternatingGroup (Fin 6)):=alternatingGroup.isSimpleGroup (by simp)
  have hfull:=normalClosure_eq_top_of_pPerfect_simple_image d.counterexample.local_component.2.1.2.1 q hq hk Y hY
  have hK:K=⊤:=top_unique (hfull ▸ normalClosure_le_normal (le_conjugateSpanBy Y P))
  have he:=congrArg (Subgroup.map L.subtype) hK
  rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hXL,subgroupOf_map_subtype,
    inf_comm,←MonoidHom.range_eq_map,range_subtype] at he
  exact he.symm

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Ordinary
