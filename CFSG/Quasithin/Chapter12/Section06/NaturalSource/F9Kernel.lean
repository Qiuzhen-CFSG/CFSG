module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Perpendicular
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Consequences
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ActionKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.GroupTheory.IndexTwoSeedKernel
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# The original F.9 normal-core kernel in Section 12.6

The literal perpendicular has index two in V. A two-perfect subgroup
fixing it modulo the central point fixes all of V. Applied to the residual
of the normal core of the point-action kernel, the original action-kernel
bridge and unique maximal two-local over LT force that residual to vanish.
Thus the normal core is contained in O₂(H), as required by F.9.1(a).

The original source hypotheses also supply both characteristic-two groups
and the trivial two-core of the generated join. The earlier fixed-space
vanishing, T-invariance and intersection bound remain explicit; no F.9
hypothesis or abelian-span conclusion is assumed here.

Source: Aschbacher--Smith, proof of 12.6.24(7), printed p.831, applying
F.9.1(a),(d), printed pp.317--318.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

omit [IsElementaryAbelian 2 V] in
include S in
/-- Both local residual and generalized Fitting conditions come from the
original maximal faithful component, before the amalgam is constructed. -/
theorem SourceHypothesis.local_residual_characteristic :
    pResidual 2 L = ⊤ ∧ generalizedFitting L = pCore 2 L := by
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let : Group.IsPerfect A := S.source.maximal_faithful.1.1.1.perfect
  have hp : IsPPerfect 2 A := (pResidual_eq_top_iff 2 A).mp
    (pResidual_eq_top_of_isPerfect 2)
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  refine ⟨(pResidual_eq_top_iff 2 L).mpr
    (hp.of_surjective e.toMonoidHom e.surjective),?_⟩
  have hh := Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T)
    (show J ∈ Chapter1.HOver G (T : Set G) from
      ⟨S.source.maximal_faithful.1.1.2.2,fun _ hx => mem_sup_right hx⟩)
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
      (normal_core_selfCentralizing (Chapter1.mem_He_iff.mp hh) A))

/-- The family membership supplies characteristic two for the original H. -/
theorem SourceHypothesis.point_local_characteristic {H : Subgroup G}
    (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    generalizedFitting H = pCore 2 H := by
  have hT : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hh := Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T)
    (show H ∈ Chapter1.HOver G (T : Set G) from ⟨hH.1.1,hT⟩)
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hh)

/-- Uniqueness of the maximal two-local over LT kills the actual generated
join's two-core for every escaping member of the original point family. -/
theorem SourceHypothesis.point_join_core_eq_bot {H : Subgroup G}
    (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    pCore 2 (L ⊔ (T : Subgroup G) ⊔ H : Subgroup G) = ⊥ := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have horb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      S.chosen.sylow_normalizes_component) (le_componentOrbit L T)
  apply sup_twoCore_eq_bot_of_unique (L ⊔ (T : Subgroup G)) H (M L) _ hH.2.2
  simpa only [horb,M] using hu.normalizer_unique
/-- The original normal core condition F.9.1(a), from the earlier
intersection bound and T-invariance of V, without an F.9 hypothesis. -/
theorem SourceHypothesis.original_point_kernel
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    let : (((D.fullSetup hZ T z).V₁).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer
        (hH.2.1.trans (Subgroup.centralizer_le_normalizer _))
    (centralizerModulo (⊤ : Subgroup H)
      (((D.fullSetup hZ T z).V₅).subgroupOf H)
      (((D.fullSetup hZ T z).V₁).subgroupOf H)).normalCore ≤ pCore 2 H := by
  let E := D.fullSetup hZ T z
  have hT : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hNV : E.G₅ ≤ normalizer (V : Set G) :=
    E.G₅_le_normalizer (E.perpendicular_card hz) hbound
  have hcontrol : H ⊓ normalizer (E.V₅ : Set G) ≤ normalizer (V : Set G) :=
    inf_le_right.trans hNV
  have hNL : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    S.chosen.normal_subgroup_normalizer_le S.source.toHypothesis1221
      (S.chosen.le_sylow.trans le_sup_right) S.chosen.ne_bot
      (sup_le S.chosen.normalizes hTV)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have horb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      S.chosen.sylow_normalizes_component) (le_componentOrbit L T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M L := by
    simpa only [horb,M] using hu.normalizer_unique
  have hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2 :=
    Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T)
      ⟨hH.1.1,hT⟩
  exact normalCore_point_kernel_le_of_index_two T L H (M L) V E.V₅ E.V₁
    S.chosen.elementary.isPGroup E.V₅_le (E.perpendicular_index hz)
    (S.chosen.le_sylow.trans hT) E.V₁_le_V₅ hH.2.1 hcontrol hT
    S.chosen.sylow_normalizes_component S.chosen.normalizes hNL
    S.centralizer_eq_core.le huniq hH.2.2 hself
end CFSG.Quasithin.Chapter12.Section06
