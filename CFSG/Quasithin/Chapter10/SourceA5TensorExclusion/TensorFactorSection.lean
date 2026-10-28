module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaChief
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.CComponent.SectionKernelCover

/-!
# The opposite tensor factor centralizes the original component section

For the literal marked tensor quotient, the first coordinate restricts on
L to its prescribed two-core quotient. An actor with trivial first coordinate
therefore has commutators with L in O₂(L). The original nonnormal orbit already
normalizes L, so the conclusion is the ambient section-centralizer statement
needed for the chosen Cartan factor in the linear tensor exclusion.

Source: Aschbacher–Smith 9.3.8, printed p.734.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual opposite-factor marking centralizes L/O₂(L). -/
theorem opposite_factor_le_sectionCentralizer
    (E : Subgroup G) (hE : E ≤ localOrbit T L)
    (hfirst : ∀ (x : G) (hx : x ∈ E), (m.quotient ⟨x,hE hx⟩).1 = 1) :
    E ≤ sectionCentralizer L := by
  have hEL : E ≤ normalizer (L : Set G) :=
    hE.trans (source_nonnormal_orbit_le_normalizer D m.sylow_not_normalizes_component)
  apply (le_sectionCentralizer_iff E L).mpr
  refine ⟨hEL,commutator_le.mpr ?_⟩
  intro x hx l hl
  have hcL : ⁅x,l⁆ ∈ L :=
    le_normalizer_iff_commutator_le_right.mp hEL (commutator_mem_commutator hx hl)
  let c : L := ⟨⁅x,l⁆,hcL⟩
  have hqc : (m.quotient ⟨⁅x,l⁆,le_componentOrbit L T hcL⟩).1 = 1 := by
    change (m.quotient ⁅(⟨x,hE hx⟩ : localOrbit T L),
      (⟨l,le_componentOrbit L T hl⟩ : localOrbit T L)⁆).1 = 1
    rw [map_commutatorElement]
    change ⁅(m.quotient ⟨x,hE hx⟩).1,
      (m.quotient ⟨l,le_componentOrbit L T hl⟩).1⁆ = 1
    rw [hfirst x hx]
    simp
  have hfc := congrArg Prod.fst (m.first_factor c)
  have hcq : QuotientGroup.mk' (pCore 2 L) c = 1 := by
    apply (map_eq_one_iff (e.trans m.firstMarking) (e.trans m.firstMarking).injective).mp
    exact hfc.symm.trans hqc
  exact mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff _).mp hcq)

include m in
/-- The original distinct Sylow conjugate supplies the opposite section factor,
without a coordinate-marking premise. -/
theorem conjugate_factor_le_sectionCentralizer
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    L.map (MulAut.conj t).toMonoidHom ≤ sectionCentralizer L := by
  let B := L.map (MulAut.conj t).toMonoidHom
  have hBR : B ≤ localOrbit T L :=
    le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨t,ht⟩
  apply (le_sectionCentralizer_iff B L).mpr
  refine ⟨hBR.trans (source_nonnormal_orbit_le_normalizer D
    m.sylow_not_normalizes_component),?_⟩
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hmapB : (A.map (MulAut.conj tH).toMonoidHom).map H.subtype = B := by
    rw [map_map,show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hc : ⁅A,A.map (MulAut.conj tH).toMonoidHom⁆ ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,hmapA,hmapB]
    exact source_conjugate_commutator_le_core D.simpleQTKE D.maximal.1 ht htn
  rw [commutator_comm] at hc
  have hc' := (section_kernel_controls_cComponent D.maximal.1.1 hc).2
  have hm := map_mono (f := H.subtype) hc'
  rwa [map_commutator,map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    hmapA,hmapB] at hm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
