module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelComplete
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Faithful
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# Faithfulness of the original outside residual

The omega-center lies in the reduced H-orbit and hence in the omega-center
of O₂(H). Since H=O²(H)T and T fixes its center, the original noncentrality
forces O²(H) to move the same seed. The normal-residual A.4.8 comparison
then proves its intrinsic signalizer module nontrivial. This supplies the
faithfulness assertion in13.2.10 before either residual-model alternative.

Source: Aschbacher–Smith13.2.10, printedp.881, and A.4.8–9.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The literal O²(H) is faithful whenever the original H moves Ω₁Z(T). -/
theorem source_residual_faithful
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ChapterA.Section04.IsFaithfulSignalizerType ((pResidual 2 H).map H.subtype) := by
  let X := (pResidual 2 H).map H.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hZH : Z ≤ H := fun z hz => hTH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  have hZU : Z ≤ omegaOrbit T H := le_conjugateSpanBy _ _
  have hZcore : Z ≤ H.pCoreIn 2 := by
    intro z hz
    exact mem_map_of_mem H.subtype (hU.le_pCore (show (⟨z,hZH hz⟩ : H) ∈
      (omegaOrbit T H).subgroupOf H from hZU hz))
  have hZomega : Z ≤ omegaOneCenterAmbient (H.pCoreIn 2) := by
    intro z hz
    refine (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hZcore hz,
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1,?_⟩
    intro q hq
    obtain ⟨q,hq,rfl⟩ := hq
    exact congrArg H.subtype (hU.le_centralizer_pCore
      (show (⟨z,hZH hz⟩ : H) ∈ (omegaOrbit T H).subgroupOf H from hZU hz) q hq)
  have hgen : X ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map,range_subtype] using hh
  have hmove : ⁅Z,X⁆ ≠ ⊥ := by
    intro he
    apply hZ
    rw [←hgen]
    refine sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)) ?_
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  let : (X.subgroupOf H).Normal := by
    have he : X.subgroupOf H = pResidual 2 H := by
      ext x
      exact mem_map_iff_mem H.subtype_injective
    rw [he]
    infer_instance
  exact Section03.Noncentrality.SupercriticalSource.faithful_signalizer_of_normal H X Z
    (Chapter1.lemma_1_1_4_6 T (d.hypothesis.qtke.evenCharacteristic T) hH.1.1)
    (map_subtype_le _) ((isPPerfect_pResidual 2).of_surjective
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).surjective) hZomega hmove
end CFSG.Quasithin.Chapter13.Section02.A5Outside
