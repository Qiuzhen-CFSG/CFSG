module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Intersection.Classification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.FixedComplete
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedInvarianceTransport
/-!
# From the original Thompson identity to full-module equality

B.2.7 places the image of L in the offender subgroup acting on the actual
full normalizer orbit. Its two-core is killed, and center-freeness makes the
induced projection from L/O₂(L) an isomorphism. The B.5 consequence therefore
applies with the original component marking, and Irr⁺ minimality identifies
the full orbit with the unchanged seed. No fixed-space assumption is used.

The actual Sp₄ and G₂ applications discharge the group exclusions in
Preliminary.Intersection. Source: Aschbacher--Smith, 11.0.3(5), printed p.760.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary

private def centerfree_quotient_equiv {A B : Type*} [Group A] [Group B]
    [IsQuasisimple (A ⧸ pCore 2 A)] [Nontrivial B]
    (f : A →* B) (hf : Function.Surjective f) (hk : pCore 2 A ≤ f.ker)
    (hz : center (A ⧸ pCore 2 A) = ⊥) : (A ⧸ pCore 2 A) ≃* B := by
  let q := QuotientGroup.lift _ f hk
  have hq : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ f hf hk
  apply MulEquiv.ofBijective q
  refine ⟨(MonoidHom.ker_eq_bot_iff q).mp ?_, hq⟩
  rcases IsQuasisimple.normal_le_center_or_eq_top q.ker with hc | ht
  · exact bot_unique (hc.trans hz.le)
  · obtain ⟨b, hb⟩ := exists_ne (1 : B)
    obtain ⟨a, rfl⟩ := hq b
    exact (hb (MonoidHom.mem_ker.mp (ht ▸ mem_top a))).elim

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem fullModule_eq_of_thompson_of_not_linear
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hcenter : center (L ⧸ pCore 2 L) = ⊥)
    (hnot : ¬ SourceCompletion.NaturalActor (L ⧸ pCore 2 L)) :
    componentOrbit V (normalizer (L : Set G)) = V := by
  let F := D.fundamentalSetup S.source.toHypothesis1221
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  obtain ⟨J, hJ, hW, hi⟩ := F.exists_internal_seed hu
  let M := F.maximalLocal
  let ρ := ReducedNormal.representation M
  let W := orbitSpan ρ ⊤ J
  let X := (Chapter3.Section02.localOrbit T L).subgroupOf M
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ J)
  have hf : Function.Surjective f := invariantActionHom_surjective ρ W _
  have hmap (A : Subgroup M) : A.map f = restrictedSubgroup ρ W A :=
    invariantActionHom_map ρ W _ A
  have hLM : L ≤ M := by rw [← D.localOrbit_eq]; exact (Chapter3.Section02.localOrbit T L).le_normalizer
  have hXcomm : X = ⁅X, Stellmacher.elementaryAbelianMaxJ (F.ambientSylow : Subgroup M)⁆ := by
    apply map_injective M.subtype_injective
    rw [map_commutator, ← Stellmacher.elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    rw [map_subgroupOf_eq_of_le (Chapter3.Section02.localOrbit T L).le_normalizer]
    change Chapter3.Section02.localOrbit T L = ⁅Chapter3.Section02.localOrbit T L,
      Stellmacher.elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf M).map M.subtype)⁆
    rw [map_subgroupOf_eq_of_le (le_normalizer_componentOrbit L T), D.localOrbit_eq]
    exact hcomm
  have hXO := reduced_actor_le_offender M F.ambientSylow W (orbitSpan_invariant ρ ⊤ J) X hXcomm
  have hXL : X = L.subgroupOf M := congrArg (fun A : Subgroup G => A.subgroupOf M) D.localOrbit_eq
  let a : X ≃* L := (MulEquiv.subgroupCongr hXL).trans (subgroupOfEquivOfLe hLM)
  let e : (X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let := S.source.quasisimple
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv e.symm
  have hn : X.map f ≠ ⊥ := by rw [hmap]; exact hi.orbit_actor_ne_bot
  let : Nontrivial (X.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
  have hXcomp : IsComponent (subspaceActionImage ρ W) (restrictedSubgroup ρ W X) := by
    have hLc : (L.subgroupOf M).IsCComponent := F.component_in_maximalLocal
    have hq : IsQuasisimple ((L.subgroupOf M) ⧸ pCore 2 (L.subgroupOf M)) := by
      rw [← hXL]
      infer_instance
    have hk : (L.subgroupOf M).pCoreIn 2 ≤ f.ker := hXL ▸ hi.orbitMap_kills_core
    rw [← hmap, hXL]
    apply hLc.isComponent_map_of_twoCore_killed hq f hf hk
    rwa [← hXL]
  have hz : center (X ⧸ pCore 2 X) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : e x ∈ center (L ⧸ pCore 2 L) := (centerCongr e ⟨x,hx⟩).property
    rw [hcenter, mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hk : pCore 2 X ≤ (f.subgroupMap X).ker := by
    intro x hx
    apply Subtype.ext
    exact hi.orbitMap_kills_core (mem_map_of_mem X.subtype hx)
  let q := centerfree_quotient_equiv (f.subgroupMap X) (f.subgroupMap_surjective X) hk hz
  have hnotX : ¬ SourceCompletion.NaturalActor (restrictedSubgroup ρ W X) := by
    rw [← hmap]
    intro hn
    exact hnot (SourceCompletion.NaturalActor.of_equiv (e.symm.trans q) hn)
  have ht := IntersectionClassification.source_seed_eq_top
    (subspaceImageRepresentation ρ W) hi.faithfulOrbit_source hXcomp hXO hnotX
  have hJW : J = W := by
    apply le_antisymm (le_orbitSpan ρ ⊤ J)
    intro v hv
    have hm : (⟨v,hv⟩ : W) ∈ J.comap W.subtype := ht ▸ Submodule.mem_top
    exact hm
  have he : F.fullModule = F.seed :=
    hW.symm.trans ((congrArg (ReducedNormal.subspaceImage M) hJW.symm).trans hJ)
  rwa [D.fundamentalSetup_fullModule, D.fundamentalSetup_seed] at he
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
