module
public import CFSG.Quasithin.Chapter10.SourceNonnormalC28
import Mathlib.Tactic

/-!
# A genuine nonnormal covering counterexample satisfies C.2.8

The section centralizer of L₀ normalizes its original component L.
Thus every eta member has the same L-orbit as its fixed covering overgroup.
The finite maximal-counterexample selection preserves that orbit, and the
actual section-centralizer Sylow supplies the complete C.2.8 configuration.
If the original T-orbit is nontrivial, its literal residual component cannot
be normal in H∩M: normalizing a component cover would normalize L itself.

This gives the exact contrary configuration to the normality conclusion
of C.4.8 in Aschbacher–Smith 4.2.12–13, printed pp.610–611, combined
manuscript of 1 March 2004. No C.4.8 conclusion is an assumption here.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Eta preserves the original component orbit through its section-centralizer factor. -/
theorem source_eta_componentOrbit
    {Mminus I : Subgroup G}
    (hI : I ∈ eta D.maximalLocal (localOrbit T L) Mminus) :
    componentOrbit L I = componentOrbit L Mminus := by
  apply le_antisymm
  · exact iSup_le fun i => le_iSup_of_le (⟨i,hI.1 i.property⟩ : Mminus) le_rfl
  · apply iSup_le
    intro m
    have hm : (m : G) ∈ (I : Set G) *
        (sectionCentralizerIn D.maximalLocal (localOrbit T L) : Set G) := by
      rw [hI.2.1]
      exact m.property
    obtain ⟨i,hi,c,hc,hic⟩ := hm
    have hcL : c ∈ normalizer (L : Set G) :=
      ((le_sectionCentralizer_iff _ _).mp (source_orbit_sectionCentralizer_le_component D)).1 hc.2
    rintro x ⟨l,hl,rfl⟩
    have hlc : c * l * c⁻¹ ∈ L := (mem_normalizer_iff.mp hcL l).mp hl
    apply (le_iSup (fun i : I => L.map (MulAut.conj (i : G)).toMonoidHom) ⟨i,hi⟩)
    refine ⟨c*l*c⁻¹,hlc,?_⟩
    change i * (c*l*c⁻¹) * i⁻¹ = (m : G) * l * (m : G)⁻¹
    rw [← hic]
    group

/-- The literal covering overgroup retains the original actor orbit. -/
theorem source_coveringOvergroup_componentOrbit
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (horbit : componentOrbit L I = localOrbit T L) :
    componentOrbit L (coveringOvergroup D.maximalLocal (localOrbit T L) I) =
      localOrbit T L := by
  apply le_antisymm
  · apply iSup_conjugates_le_of_le_normalizer _ _ _ (le_componentOrbit L T)
    exact sup_le hIM inf_le_left
  · apply horbit.symm.le.trans
    exact iSup_le fun i => le_iSup_of_le
      (⟨i,(show I ≤ coveringOvergroup D.maximalLocal (localOrbit T L) I from le_sup_left)
        i.property⟩ : coveringOvergroup D.maximalLocal (localOrbit T L) I) le_rfl

/-- Failure of source uniqueness selects a maximal counterexample retaining its orbit. -/
theorem source_covering_maximal_counterexample
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L)
    (hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal) :
    ∃ J H : Subgroup G,
      J ∈ muStar D.maximalLocal (localOrbit T L)
        (coveringOvergroup D.maximalLocal (localOrbit T L) I) ∧
      PushLE (localOrbit T L) I J ∧
      IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ D.maximalLocal ∧
      componentOrbit L J = localOrbit T L := by
  have hyp := source_orbit_hypothesis411 D
  obtain ⟨J,H,hJ,hIJ,hH,hJH,hout,_⟩ := maximal_counterexample_of_component_cover
    D.simpleQTKE hyp.maximal hyp.plus_le le_rfl hIM hcover hcore hnot
  refine ⟨J,H,hJ,hIJ,hH,hJH,hout,?_⟩
  exact (source_eta_componentOrbit D hJ.1.1).trans
    (source_coveringOvergroup_componentOrbit D hIM horbit)

/-- The original nonnormal covering counterexample gives strict C.2.8 with a nonnormal component. -/
theorem source_covering_counterexample_C28
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L)
    (hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
      PushLE (localOrbit T L) I J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ D.maximalLocal < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ D.maximalLocal)
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) (J.pCoreIn 2)
        (fullModule (localOrbit T L)
          ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
            (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
      ¬ H ⊓ D.maximalLocal ≤ normalizer
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype : Set G) := by
  obtain ⟨hs,_⟩ := coveringOvergroup_eta (localOrbit T L).le_normalizer le_rfl hIM hcover hcore
  obtain ⟨J,H,hJ,hIJ,hH,hJH,hout,hJo⟩ :=
    source_covering_maximal_counterexample D hIM hcover hcore horbit hnot
  have hyp := source_orbit_hypothesis411 D
  have hJC := core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hs.1 hJ.1.1
  let C := sectionCentralizerIn D.maximalLocal (localOrbit T L)
  obtain ⟨S,hRS⟩ := ((isPGroup_pCoreIn 2 J).comap_subtype :
    IsPGroup 2 ((J.pCoreIn 2).subgroupOf C)).exists_le_sylow
  have hRS' : J.pCoreIn 2 ≤ (S : Subgroup C).map C.subtype := by
    intro x hx
    exact ⟨⟨x,hJC hx⟩,hRS hx,rfl⟩
  have hlt : H ⊓ D.maximalLocal < H :=
    lt_of_le_not_ge inf_le_left (fun he => hout (he.trans inf_le_right))
  refine ⟨J,H,S,hIJ,hH,hJH,hlt,
    source_nonnormal_C28_of_muStar D hs hJ hH hJH hout hJo S hRS',?_⟩
  intro hnorm
  have hJM : J ≤ D.maximalLocal := hJ.1.1.1.trans hs.1
  have hcoverL := (source_covering_intersection_component D hJM hJH hJ.1.1.2.2.1).2
  have hJL : J ≤ normalizer (L : Set G) :=
    (le_inf hJM ((le_inf hJH hJM).trans hnorm)).trans
      (source_component_cover_normalizer D ((map_subtype_le _).trans inf_le_left) hcoverL.subset)
  have he : localOrbit T L = L := hJo.symm.trans
    (le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hJL)
      (le_componentOrbit L J))
  apply hn
  have hT := le_normalizer_componentOrbit L T
  change (T : Subgroup G) ≤ normalizer (localOrbit T L : Set G) at hT
  rwa [he] at hT
end CFSG.Quasithin.Chapter10
