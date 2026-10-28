module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.ModuleLayers
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.EscapingConjugate

/-!
# C.5.5 for the original block modules

The C.5.3 blocks give the literal U-layers. Their embedded core bounds
place them in the original R, while the C.1.11 module calculation supplies
both the commutator and centralizer bounds used by the escaping-conjugate
argument. Thus no module-core identity or moving element remains an input.

Source: Aschbacher–Smith C.5.4(4) and C.5.5, printed p.155.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
universe u
variable {G : Type u} [Group G] [Finite G]
variable {H M K R T : Subgroup G}

/-- The original U-layer as a subgroup of the ambient G. -/
def ambientModule (L : Subgroup H) : Subgroup G := (moduleLayer L).map H.subtype

omit [Finite G] in
theorem ambientModule_eq_literal (L : Subgroup H) :
    ambientModule L = moduleLayer (L.map H.subtype) :=
  (moduleLayer_map H.subtype H.subtype_injective L).symm

theorem OriginalHypotheses.module_le_R (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i : Fin b.size) : ambientModule (b.block i) ≤ R := by
  have hUK : ambientModule (b.block i) ≤ K := by
    exact (map_mono ((moduleLayer_le _).trans
      ((le_iSup b.block i).trans b.generate.le))).trans_eq d.residual
  have hUQ : ambientModule (b.block i) ≤ H.pCoreIn 2 :=
    map_mono (moduleLayer_le_core (b.type i).1)
  have hURK := (le_inf (hUK.trans le_sup_right) hUQ).trans
    (inf_pCoreIn_le_of_le 2 (sup_le d.R_le_H d.K_le_H))
  exact hURK.trans ((pCoreIn_le_sylow (R ⊔ K) d.residual_sylow).trans_eq
    d.residual_sylow_image)

omit [Finite G] in
theorem OriginalHypotheses.module_orbit (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i₀ : Fin b.size) : ∀ i, ∃ t ∈ T,
      ambientModule (b.block i) =
        (ambientModule (b.block i₀)).map (MulAut.conj t⁻¹).toMonoidHom := by
  intro i
  obtain ⟨t,ht,he⟩ := b.transitive i₀ i
  refine ⟨(t : G),d.sylow_image ▸ mem_map_of_mem H.subtype ht,?_⟩
  rw [ambientModule,he,moduleLayer_map _ (MulAut.conj t⁻¹).injective,
    Subgroup.map_map,ambientModule,Subgroup.map_map]
  rfl

/-- The actual C.5.5 noncommuting conjugate, for any selected member of
the original C.5.3 family. -/
theorem OriginalHypotheses.exists_noncommuting_module
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i₀ : Fin b.size) : ∃ x ∈ M,
      ⁅ambientModule (b.block i₀),
        (ambientModule (b.block i₀)).map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ := by
  let U : Fin b.size → Subgroup G := fun i => ambientModule (b.block i)
  have hU : U i₀ ≠ ⊥ := fun he => moduleLayer_ne_bot (b.type i₀).1.short
    ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)
  have hcomm : ⁅H.pCoreIn 2,K⁆ ≤ ⨆ i,U i := by
    have hh := map_mono (f := H.subtype)
      (core_commutator_le_moduleJoin b.block (fun i => (b.type i).1))
    rw [map_commutator,b.generate,d.residual,Subgroup.map_iSup] at hh
    exact hh
  have hcentralizer : R ⊓ centralizer ((⨆ i,U i : Subgroup G) : Set G) ≤ H.pCoreIn 2 := by
    intro x hx
    have hxH := d.R_le_H hx.1
    have hxC : (⟨x,hxH⟩ : H) ∈
        centralizer ((⨆ i,moduleLayer (b.block i) : Subgroup H) : Set H) := by
      intro y hy
      apply Subtype.ext
      apply hx.2
      have hy' := mem_map_of_mem H.subtype hy
      rw [Subgroup.map_iSup] at hy'
      exact hy'
    have hc := centralizer_moduleJoin_le_core b.block (fun i => (b.type i).1)
      d.fitting b.generate hxC
    exact mem_map_of_mem H.subtype hc
  exact exists_noncommuting_conjugate M H K R (H.pCoreIn 2) T U i₀
    d.H_le_residual_sup_M d.R_le_M d.T_le d.R_normal d.no_common_normal hU
    (d.module_le_R b i₀) (d.module_orbit b i₀) hcomm hcentralizer

/-- Original C.5.3 and C.5.5 assembled: the block family and moving
conjugator are constructed from C.5.1–2 and the genuine earlier source. -/
theorem OriginalHypotheses.blocks_and_noncommuting_conjugate
    (d : OriginalHypotheses H M K R T) {𝒦 : GroupClass.{u}}
    (outside : C128Outside 𝒦) (hG : IsSQTK 𝒦 G) :
    ∃ b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H),
      ∃ i₀ : Fin b.size, ∃ x ∈ M,
        ⁅moduleLayer ((b.block i₀).map H.subtype),
          (moduleLayer ((b.block i₀).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ := by
  obtain ⟨b⟩ := d.block_decomposition outside hG
  let i₀ : Fin b.size := ⟨0,b.positive⟩
  obtain ⟨x,hx,hnc⟩ := d.exists_noncommuting_module b i₀
  rw [ambientModule_eq_literal] at hnc
  exact ⟨b,i₀,x,hx,hnc⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
