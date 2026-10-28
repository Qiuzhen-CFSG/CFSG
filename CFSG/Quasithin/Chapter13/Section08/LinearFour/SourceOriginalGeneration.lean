module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.PlaneClosure
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoveredSeed
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.Constructions

/-!
# The original local generators of the covered A₆ component

The natural six-letter action makes the point normalizer maximal in L.
The original plane residual escapes that normalizer. A Sylow decomposition
of the point normalizer puts it inside the join of L₁ and N_L(V₂): the
point residual lies in L by the covered factorization, and the remaining
Sylow element normalizes V₂. Thus those two literal subgroups generate L.

The maximality transport follows the natural-coordinate argument in
Section05/PlaneGeometry/TwoBlocks/SourceContainment/ParabolicGeneration;
its ordinary-quotient hypothesis is unnecessary for this local conclusion.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.2.2(3), 13.5.4 and the generating subgroups used in 13.8.30,
printed pp.877,916,964.
-/

public noncomputable section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion Section07.NaturalAction
open Section05 Section05.PlaneGeometry Section05.PlaneGeometry.TwoBlocks
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
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


/-- The original point residual and the relative plane normalizer generate
L. The normalizers and the residual retain their actual ambient meanings. -/
theorem source_original_local_generators
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) :
    (sourceOne L T V₁).subgroupOf L ⊔ (G2 V₂).subgroupOf L = ⊤ := by
  let J := (sourceOne L T V₁).subgroupOf L ⊔ (G2 V₂).subgroupOf L
  let P := (normalizer (V₁:Set G)).subgroupOf L
  have hmax : IsCoatom P := point_normalizer_maximal d
  have h1L : sourceOne L T V₁ ≤ L :=
    LocalAction.one_le_L_of_factorization L T V₁ d.normalizes_L
      (Section07.ModelExclusions.covered_factorization d ⟨eL⟩)
  have hPJ : P ≤ J := by
    intro x hx
    let A := (L ⊔ (T:Subgroup G)) ⊓ normalizer (V₁:Set G)
    have hTA : (T:Subgroup G) ≤ A := le_inf le_sup_right d.line_stable
    let xA : A := ⟨x,mem_sup_left x.property,hx⟩
    have hall := pResidual_sup_sylow_eq_top (T.subtype hTA)
    obtain ⟨a,ha,t,ht,hat⟩ := mem_sup_of_normal_left.mp (hall.symm ▸ mem_top xA)
    have ha1 : (a:G) ∈ sourceOne L T V₁ := mem_map_of_mem A.subtype ha
    have hat' : (a:G) * (t:G) = (x:G) := congrArg Subtype.val hat
    have htL : (t:G) ∈ L := by
      rw [←inv_mul_cancel_left (a:G) (t:G),hat']
      exact L.mul_mem (L.inv_mem (h1L ha1)) x.property
    have htT : (t:G) ∈ (T:Subgroup G) := ht
    have he : (⟨a,h1L ha1⟩:L) * ⟨t,htL⟩ = x := Subtype.ext hat'
    rw [←he]
    exact mul_mem_sup ha1 (d.plane_stable htT)
  apply hmax.2
  refine lt_of_le_of_ne hPJ ?_
  intro he
  apply Section05.PlaneGeometry.planeActor_not_normalizes_line d
  intro x hx
  have hxL : x ∈ L :=
    (Section05.PlaneGeometry.TwoBlocks.planeActor_le.trans inf_le_left) hx
  have hx2 : x ∈ G2 V₂ :=
    (Section05.PlaneGeometry.TwoBlocks.planeActor_le.trans inf_le_right) hx
  have hh : (⟨x,hxL⟩:L) ∈ P := he.symm ▸ (show (⟨x,hxL⟩:L) ∈ J from mem_sup_right hx2)
  exact hh

end CFSG.Quasithin.Chapter13.Section08.LinearFour
