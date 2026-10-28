module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryThompsonSolvable
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonEscape

/-!
# The original odd-core or quotient-component escape

Apply all five adequate B.5.6 alternatives to the actual Thompson image of
the reduced omega-center orbit. Its two-residual lies in the layer times
the full three-core. The original Sylow subgroup already lies in M, so
an escaping Thompson subgroup forces one of those two factors to escape.
The component retains its inclusion in both the Thompson image and the
ambient action quotient. Every containment test uses the full inverse image
under the original centralizer quotient map, followed by H's inclusion in G.

This establishes the first dichotomy on printed p.707. Odd-core exclusion,
quotient-component lifting and exclusion, ambient containment, and final
non-FF assembly remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of Proposition 7.7.3, printed p.707,
refs/quasithin.pdf; B.5.6, printed p.105.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original escaping H has either an escaping full three-core preimage
or an escaping ordinary quotient-component preimage, on the same doubled orbit. -/
theorem sourceOrbit_binary_pairedPlane_thompson_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          HasMarking D.sourceOrbit L E ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype = R) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar B (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧
              (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = R) ∧
              H.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
              H = elementaryAbelianMaxJ H ⊔ B ∧
              H ⊓ normalizer (L : Set G) ∈ Chapter1.He G ∧
              HasCharacteristicTwo H ∧ generalizedFitting H = pCore 2 H ∧
              Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H
                ((L ⊔ (T : Subgroup G)).pCoreIn 2) (H ⊓ normalizer (L : Set G)) ∧
              let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
              D.sourceOrbit ≤ Y ∧ ∃ hred : IsPReduced 2 (Y.subgroupOf H),
              centralizer (Y : Set G) ≤ normalizer (L : Set G) ∧
              ¬ elementaryAbelianMaxJ H ≤ centralizer (Y : Set G) ∧
              inducedAutomizer Y (elementaryAbelianMaxJ H) ≠ ⊥ ∧
              DoubledBinaryThompson.ReducedThompsonAlternative (Y.subgroupOf H) hred ∧
              ¬ DoubledBinaryThompsonPlanes.ReducedSymmetricThree (Y.subgroupOf H) hred ∧
              DoubledBinaryThompsonRelativePlanes.RelativePlaneFactorsContained (Y.subgroupOf H) hred
                ((localResidual L U).subgroupOf H)
                ((normalizer (L : Set G)).subgroupOf H) ∧
              let := hred.normal
              let J := DoubledBinaryThompson.thompsonImage (Y.subgroupOf H)
              let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
              ¬ Group.IsSolvable J ∧
              (¬ (((pCore 3 J).map J.subtype).comap q).map H.subtype ≤ normalizer (L : Set G) ∨
                ∃ K : Subgroup J, IsComponent J K ∧
                  IsComponent (ChapterB.InternalThompsonAction.ActionQuotient (Y.subgroupOf H))
                    (K.map J.subtype) ∧
                  ¬ ((K.map J.subtype).comap q).map H.subtype ≤ normalizer (L : Set G))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_thompson_nonsolvable h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let M := normalizer (L : Set G)
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol⟩ := hescape hout
  refine ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,?_⟩
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let := hred.normal
  let := hred.elementary
  have hBM : B ≤ M := hbase.trans_le (inf_le_left.trans
    (sup_le L.le_normalizer D.sylow_normalizes_component))
  have hJM : ¬ elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    intro hj
    have hh := map_mono (f := H.subtype) hj
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      ← MonoidHom.range_eq_map,range_subtype] at hh
    have hJH : elementaryAbelianMaxJ H ≤ M :=
      hh.trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
    apply hH.1.2
    rw [hgen]
    exact sup_le hJH hBM
  have hPM : (P : Subgroup H) ≤ M.subgroupOf H :=
    map_le_iff_le_comap.mp (hP.trans_le (le_sup_right.trans hBM))
  have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hkernel : centralizer (Y.subgroupOf H : Set H) ≤ M.subgroupOf H := by
    intro a ha
    apply hcent
    intro y hy
    exact congrArg Subtype.val (ha ⟨y,hYH hy⟩ hy)
  have hh := DoubledBinaryThompsonEscape.thompson_oddCore_or_component_escape
    (Y.subgroupOf H) P (M.subgroupOf H) hSQ hred.quotient_pCore_eq_bot hPM hkernel hJM
  rcases hh with h3 | ⟨K,hK,hKA,hKM⟩
  · exact Or.inl (fun he => h3 (map_le_iff_le_comap.mp he))
  · exact Or.inr ⟨K,hK,hKA,fun he => hKM (map_le_iff_le_comap.mp he)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
