module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.EvenSylowNormalizer
public import Theory.GroupTheory.PResidual.SylowKernelCentralizer
public import Theory.GroupTheory.SylowKernelCore
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure.CubicActors

/-!
# The original E.2.1 escape from the kernel residual

Transport the actual R=O₂(XT) between H and the ambient G. Its Thompson
normalizer bound rules out R=O₂(H), while the intrinsic commutator argument
puts R in C_T(J/O₂(H)). As J is the proved original omega-action kernel,
this is exactly the second E.2.1 hypothesis. The whole S₃/wreath actor
then specializes the full source theorem to its three cubic models.

The sole extra step retained here is the actual even action of R on the
chosen A₅ module, the preceding inner-action argument of 13.2.9.
Source: Aschbacher–Smith 13.2.9 and E.2.1, printed pp. 880–881 and 215.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
open Stellmacher Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The constructed R forces the second original E.2.1 escape alternative. -/
theorem source_kernel_e21_escape_of_even_action
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    let R := (X ⊔ (T : Subgroup G)).pCoreIn 2
    let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
    (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5) →
      ¬ centralizerModulo (T.subtype hH.1.1.2 : Subgroup H)
          (ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) h.2.2.1)
          (pCore 2 H) ≤ pCore 2 H := by
  dsimp only
  intro heven
  let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let C := centralizer (U : Set H)
  let S := T.subtype hH.1.1.2
  let X := (pResidual 2 C).map C.subtype
  let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
  let XG := X.map H.subtype
  let RG := (XG ⊔ (T : Subgroup G)).pCoreIn 2
  have hTC : (S : Subgroup H) ⊓ C = pCore 2 H :=
    (ChapterE.ThompsonAction.reduced_centralizer_sylow S h.2.2.1 U hU h.2.2.2.2).1
  obtain ⟨hQR,hRT,hRC,hcent⟩ := residual_sylow_core_centralizes S C hTC
  have hRmap : R.map H.subtype = RG := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective]
    congr 1
    rw [Subgroup.map_sup]
    change XG ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = XG ⊔ (T : Subgroup G)
    rw [map_subgroupOf_eq_of_le hH.1.1.2]
  have hN : normalizer (elementaryAbelianMaxJ RG : Set G) ≤ normalizer (L : Set G) :=
    (source_kernel_thompson_normalizer_of_even_action d hH hB hZ hs hne heven).2
  have hnot : ¬ R ≤ pCore 2 H := by
    intro hle
    have he : R = pCore 2 H := le_antisymm hle hQR
    have heG : RG = H.pCoreIn 2 := by rw [←hRmap,he]; rfl
    have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    rw [heG] at hN
    exact hH.1.2 ((hn.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)).trans hN)
  have heC : ChapterB.minimalParabolicCore S h.2.2.1 = C :=
    source_core_eq_omega_centralizer d hH hB hZ hs
  intro hc
  apply hnot
  change centralizerModulo (S : Subgroup H) (ChapterB.minimalParabolicCore S h.2.2.1)
      (pCore 2 H) ≤ pCore 2 H at hc
  rw [heC] at hc
  exact hcent.trans hc

/-- Full E.2.1 now classifies the literal residual in H/O₂(H), using the
proved whole natural actor; the preceding even-action step remains explicit. -/
theorem source_kernel_cubic_models_of_even_action
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    let R := (X ⊔ (T : Subgroup G)).pCoreIn 2
    (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5) →
      ChapterE.SolvableMinimalParabolic.CubicResidualModels H := by
  dsimp only
  intro heven
  let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  have hescape := source_kernel_e21_escape_of_even_action d hH hB hZ hs hne heven
  have hx : ¬ centralizerModulo (T.subtype hH.1.1.2 : Subgroup H)
      (ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) h.2.2.1)
      ((ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) h.2.2.1).pCoreIn 2) ≤ pCore 2 H := by
    intro hc
    apply hescape
    intro t ht
    apply hc
    apply mem_centralizerModulo_iff.mpr
    obtain ⟨htS,htC⟩ := mem_centralizerModulo_iff.mp ht
    refine ⟨htS,?_⟩
    intro j hj
    rw [ChapterE.SolvableMinimalParabolic.core_pCoreIn_eq]
    exact htC j hj
  apply ChapterE.SolvableMinimalParabolic.source_cubic_models_of_centralizer_quotient
    h.1 (T.subtype hH.1.1.2) h.2.2.1 hs (Or.inr hx) U
  rcases source_solvable_wreath_omega_action d hH hB hZ hs with ⟨c,e,he⟩ | ⟨e,c,he⟩
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
