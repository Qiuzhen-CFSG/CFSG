module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalIndex
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SourceSylow

/-!
# Full-Sylow normalization on the characteristic replacement

The original odd-index witness gives a full Sylow which normalizes the
characteristic replacement radical. Restriction to its normal overgroup
and edge transport give this same property at every original-group vertex.
Sylow conjugacy then marks the quotient so the standard unipotent group
normalizes the edge image, with the exact full-layer fixed indices retained.

This strengthens the coordinates used for MS93 (5.1), printed p.913, using
the original Section 7 input. It does not give the replacement an odd-index
radical witness or assert that its edge is itself Sylow.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
/-- The replacement edge lies in a full Sylow which normalizes it. -/
theorem Input.replacement_edge_normalizing_sylow
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ P : Sylow 2 (stabilizer d.radical a),
      (Q d.radical t).subgroupOf (stabilizer d.radical a) ≤ (P : Subgroup (stabilizer d.radical a)) ∧
      (P : Subgroup (stabilizer d.radical a)) ≤ normalizer
        ((Q d.radical t).subgroupOf (stabilizer d.radical a) : Set (stabilizer d.radical a)) := by
  obtain ⟨S,_,_,hTS,hSn⟩ := h.exists_replacement_normalizing_sylow d
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal d.overgroup
    (h.replacement_normal d).isSubnormal
  have hTP : d.radical ≤ (P : Subgroup d.overgroup) := by
    rw [hP]
    exact comap_mono hTS
  have hPn : (P : Subgroup d.overgroup) ≤ normalizer (d.radical : Set d.overgroup) := by
    rw [hP]
    exact (comap_mono hSn).trans (d.ambient.le_normalizer_comap d.overgroup.subtype)
  obtain ⟨j,hj,hjr,hjR,_,_⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  let V := stabilizer d.radical a
  let jV : d.overgroup →* V := j.codRestrict V (fun x => by
    change j x ∈ stabilizer d.radical a
    rw [←hjr]
    exact ⟨x,rfl⟩)
  have hjV : Function.Surjective jV := by
    intro x
    obtain ⟨y,hy⟩ := (show x.val ∈ j.range from hjr.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  have hT : d.radical.map jV = (Q d.radical t).subgroupOf V := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hjR ▸ mem_map_of_mem j hy
    · intro hx
      obtain ⟨y,hy,he⟩ := (show x.val ∈ d.radical.map j from hjR.symm ▸ hx)
      exact ⟨y,hy,Subtype.ext he⟩
  refine ⟨P.mapSurjective (f := jV) hjV,?_,?_⟩
  · change _ ≤ (P : Subgroup d.overgroup).map jV
    rw [←hT]
    exact map_mono hTP
  · change (P : Subgroup d.overgroup).map jV ≤ _
    rw [←hT]
    exact (map_mono hPn).trans (le_normalizer_map jV)

/-- Coordinates preserving normalization by the whole standard Sylow. -/
theorem Input.replacement_normalized_small_mover_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        unipotent ≤ normalizer
          (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp E.Carrier)) ∧
        ∀ A : Subgroup (stabilizer d.radical a), A ≤ (Q d.radical t).subgroupOf (stabilizer d.radical a) →
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            movingIndex ((A.map f).subgroupOf unipotent) := by
  obtain ⟨E,hE,f,hf,hfQ,hidx⟩ := h.replacement_inner_natural_indices d geometry hb ha
  let := finite_stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf (stabilizer d.radical a)
  obtain ⟨P,hTP,hPn⟩ := h.replacement_edge_normalizing_sylow d ha hat
  let S := P.mapSurjective (f := f) hf
  have hS : T.map f ≤ (S : Subgroup _) := map_mono hTP
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E.Carrier) S
    (unipotentSylow (by rw [E.card_eq]) (by rw [hE]; exact h.nonbinary.le))
  have hSm : (S : Subgroup (Sp E.Carrier)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun S : Sylow 2 (Sp E.Carrier) => (S : Subgroup (Sp E.Carrier))) hg
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact (map_mono hS).trans_eq hSm
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  refine ⟨E,hE,f',(MulAut.conj g).surjective.comp hf,by rw [hker]; exact hfQ,hTf,?_,?_⟩
  · have hh := (map_mono (f := f) hPn).trans (le_normalizer_map f)
    have hh' := (map_mono (f := (MulAut.conj g).toMonoidHom) hh).trans
      (le_normalizer_map (MulAut.conj g).toMonoidHom)
    change ((S : Subgroup _).map (MulAut.conj g).toMonoidHom) ≤ _ at hh'
    rw [hSm,Subgroup.map_map] at hh'
    exact hh'
  ·
    intro A hAT
    have hAf : A.map f' ≤ unipotent := (map_mono hAT).trans hTf
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have hi : (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) = 2 ^ fixedCodim τ (A.map f') := by
      rw [←Subgroup.map_map, fixedCodim_map_conj]
      exact hidx A
    rw [hi,←binary_movingIndex]
    congr 1
    have hcomp : restrictScalars (k := ZMod 2) (natural (F := E.Carrier)) =
        τ.comp (unipotent (F := E.Carrier)).subtype := rfl
    rw [hcomp]
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,map_subgroupOf_eq_of_le hAf]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
