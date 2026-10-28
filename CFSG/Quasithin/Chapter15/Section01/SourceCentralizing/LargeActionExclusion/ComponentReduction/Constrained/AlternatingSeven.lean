module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenCoordinates
public import Theory.Representation.BinaryPermutation.PairedResidual

/-!
# Literal partition residual and natural action of the constrained A₇ block

The partition in the alternative lifts through the original two-core quotient
into M ∩ L: its kernel is in the selected Sylow. Residual functoriality then
identifies the same partition's two-residual and proves its centralization
by V₁. Whole-module automorphism coordinates give the actual seven-letter
action, where the original index-two control excludes the triple transposition.

These are steps of the ordinary block exclusion, not its conclusion. The
partition centralizer must still be transferred in these same coordinates,
and the A₆ point-stabilizer residual must supply the final contradiction.
Both remain local obligations of qt-e-1515-constrained-linear-quotient.
Source: Aschbacher--Smith 15.1.25(5), printed p.1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem ExchangedSource.constrained_a7_normalizes {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (a : d.ConstrainedA7Alternative) :
    d.S ≤ normalizer (d.L : Set G) := by
  have he := (s.constrained_a7_residual_and_movement hG h a.block).1
  conv_rhs => rw [he]
  exact d.S_le_G1.trans (d.G1.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _)))

theorem ExchangedSource.a7_partition_preimage_le {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hTM : (T : Subgroup G) ≤ M)
    (e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1])
    (f : d.L →* Equiv.Perm (Fin 7))
    (hf : f = (alternatingGroup (Fin 7)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))))
    (hp : alternatingGroup (Fin 7) ⊓ p.stabilizer ≤ ((M ⊓ d.L).subgroupOf d.L).map f) :
    (p.stabilizer.comap f).map d.L.subtype ≤ M ⊓ d.L := by
  have hk : f.ker = pCore 2 d.L := by
    rw [hf,MonoidHom.ker_comp_of_injective _ _ (alternatingGroup (Fin 7)).subtype_injective,
      MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkM : f.ker ≤ (M ⊓ d.L).subgroupOf d.L := by
    rw [hk]
    obtain ⟨P,hP⟩ := s.component_sylow
    have hcore : d.L.pCoreIn 2 ≤ d.SL := hP ▸ pCoreIn_le_sylow d.L P
    intro l hl
    exact ⟨hTM (d.S_le_T (d.SL_le_S (hcore (mem_map_of_mem d.L.subtype hl)))),l.property⟩
  rintro g ⟨l,hl,rfl⟩
  have hh : f l ∈ ((M ⊓ d.L).subgroupOf d.L).map f := hp ⟨by
    rw [hf]; exact (e (QuotientGroup.mk' _ l)).property,hl⟩
  have hc : l ∈ (((M ⊓ d.L).subgroupOf d.L).map f).comap f := hh
  rw [Subgroup.comap_map_eq,sup_eq_left.mpr hkM] at hc
  exact hc

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem a7_partition_residual_image (d : CaseIComponentData T M Mc V)
    (e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1]) :
    let f := (alternatingGroup (Fin 7)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
    let P := p.stabilizer.comap f
    ((pResidual 2 P).map P.subtype).map f =
      (pResidual 2 (alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup _)).map
        (alternatingGroup (Fin 7) ⊓ p.stabilizer).subtype := by
  intro f P
  have hr : f.range = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro g ⟨l,rfl⟩
      exact (e (QuotientGroup.mk' _ l)).property
    · intro g hg
      obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) ⟨g,hg⟩
      exact ⟨l,congrArg Subtype.val hl⟩
  rw [map_embedded_pResidual]
  have he : P.map f = alternatingGroup (Fin 7) ⊓ p.stabilizer := by
    rw [Subgroup.map_comap_eq,hr,inf_comm]
  rw [he]

theorem a7_partition_residual_fixed (d : CaseIComponentData T M Mc V) (P : Subgroup d.L)
    (hP : P.map d.L.subtype ≤ M ⊓ d.L) :
    d.nineFixedPlane ≤ centralizer
      ((((pResidual 2 P).map P.subtype).map d.L.subtype) : Set G) := by
  rw [map_embedded_pResidual]
  exact inf_le_right.trans (centralizer_le (embedded_pResidual_mono 2
    (hP.trans (inf_le_inf_left M d.L_component.1))))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem a7_block_module_coordinates {d : CaseIComponentData T M Mc V}
    (E : blockU d.L ≃* Multiplicative (BinaryPermutation.core (Fin 7)))
    (f : MulAut d.L →* Equiv.Perm (Fin 7))
    (hE : ∀ a u, (E (MulAut.characteristic (blockU d.L) a u)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 7) (f a) (E u).toAdd) :
    ∃ e : (blockU d.L).map d.L.subtype ≃*
        Multiplicative (BinaryPermutation.core (Fin 7)),
      ∀ (a : normalizer (d.L : Set G)) (u : (blockU d.L).map d.L.subtype),
        (e.symm (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 7)
            (f (d.L.normalizerMonoidHom a)) (e u).toAdd)) : G) =
              (a : G) * (u : G) * (a : G)⁻¹ := by
  let j := (blockU d.L).equivMapOfInjective d.L.subtype d.L.subtype_injective
  let e := j.symm.trans E
  refine ⟨e,?_⟩
  intro a u
  let w := j.symm u
  have hw : (((w : blockU d.L) : d.L) : G) = u := congrArg Subtype.val (j.apply_symm_apply u)
  have he : e (j (MulAut.characteristic (blockU d.L) (d.L.normalizerMonoidHom a) w)) =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 7)
        (f (d.L.normalizerMonoidHom a)) (e u).toAdd) := by
    apply Multiplicative.toAdd.injective
    change (E (j.symm (j (MulAut.characteristic (blockU d.L)
      (d.L.normalizerMonoidHom a) w)))).toAdd = _
    rw [j.symm_apply_apply]
    exact hE _ _
  rw [←he,e.symm_apply_apply]
  change (a : G) * (((w : blockU d.L) : d.L) : G) * (a : G)⁻¹ = _
  rw [hw]

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual partition supplied by the alternative lifts into the selected
parabolic. Its two-residual has the literal model image and centralizes V₁. -/
theorem ConstrainedA7Alternative.partition_residual
    {d : CaseIComponentData T M Mc V} (a : d.ConstrainedA7Alternative)
    (s : d.ExchangedSource) (hTM : (T : Subgroup G) ≤ M) :
    ∃ e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
    ∃ p : Partition 7 4 ![2,2,2,1],
      let f := (alternatingGroup (Fin 7)).subtype.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
      let P := p.stabilizer.comap f
      (d.SL.subgroupOf d.L).map f ≤ p.stabilizer ∧
      P.map d.L.subtype ≤ M ⊓ d.L ∧
      ((pResidual 2 P).map P.subtype).map f =
        (pResidual 2 (alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup _)).map
          (alternatingGroup (Fin 7) ⊓ p.stabilizer).subtype ∧
      d.nineFixedPlane ≤ centralizer
        ((((pResidual 2 P).map P.subtype).map d.L.subtype) : Set G) := by
  obtain ⟨e,p,hs,hp⟩ := a.partition
  have hP := s.a7_partition_preimage_le hTM e p _ rfl hp
  exact ⟨e,p,hs,hP,a7_partition_residual_image d e p,a7_partition_residual_fixed d _ hP⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData


open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The permutation actor and the actual whole block module share one quotient
marking. Original index-two control excludes the triple transposition. -/
theorem ExchangedSource.constrained_a7_marked_action
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hb : IsAlternatingBlock d.L 7) :
    ∃ q : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
    ∃ E : (blockU d.L).map d.L.subtype ≃*
        Multiplicative (BinaryPermutation.core (Fin 7)),
    ∃ f : normalizer (d.L : Set G) →* Equiv.Perm (Fin 7),
      (∀ l : d.L, f ⟨l,d.L.le_normalizer l.property⟩ =
        (q (QuotientGroup.mk' (pCore 2 d.L) l)).val) ∧
      (∀ (a : normalizer (d.L : Set G)) (u : (blockU d.L).map d.L.subtype),
        (E.symm (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 7) (f a) (E u).toAdd)) : G) =
              (a : G) * (u : G) * (a : G)⁻¹) ∧
      ∀ v ∈ d.nineFixedPlane, ∀ hv : v ∈ normalizer (d.L : Set G),
        (f ⟨v,hv⟩).cycleType ≠ {2,2,2} := by
  obtain ⟨q,E0,f0,hq,hE0⟩ := hb.seven_automorphism_coordinates
  obtain ⟨E,hE⟩ := a7_block_module_coordinates (d := d) E0 f0 hE0
  let f := f0.comp d.L.normalizerMonoidHom
  refine ⟨q,E,f,?_,hE,?_⟩
  · intro l
    have hh : d.L.normalizerMonoidHom ⟨l,d.L.le_normalizer l.property⟩ = MulAut.conj l := by
      ext k
      rfl
    exact (congrArg f0 hh).trans (hq l)
  · intro v hv hvL heq
    have hUS : (blockU d.L).map d.L.subtype ≤ d.S := by
      obtain ⟨P,hP⟩ := s.component_sylow
      have hc : d.L.pCoreIn 2 ≤ d.SL := hP ▸ pCoreIn_le_sylow d.L P
      exact ((map_mono blockU_le_core).trans hc).trans d.SL_le_S
    apply AlternatingSeven.ThreeResidualLocals.not_triple_of_plane_index_two
      d.S d.nineFixedPlane ((blockU d.L).map d.L.subtype) hUS
      s.fixed_centralizer_index v hv (f ⟨v,hvL⟩) heq E
    intro u
    have hh := hE ⟨v,hvL⟩ u
    change (E.symm (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 7) (f ⟨v,hvL⟩) (E u).toAdd)) : G) =
        v * (u : G) * v⁻¹ at hh
    exact hh

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
