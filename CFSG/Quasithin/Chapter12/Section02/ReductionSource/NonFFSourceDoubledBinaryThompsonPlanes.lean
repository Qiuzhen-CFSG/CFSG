module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOmega
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonPlanes

/-!
# Excluding the symmetric-three Thompson image on the original orbit

The original two-residual normalizes J(T₀)=J(Q)=J(T). On the binary plane
moved by a symmetric-three Thompson image, its action must therefore be
trivial. The image centralizes [W,L₀]; together with its fixation of the
original paired plane this centralizes all of W. Thompson generation then
puts H in M, contradicting its original minimal escape.

The other Thompson alternatives, ambient containment and the final non-FF
contradiction remain with qt-d-1222-nonff-doubled. This does not eliminate
the mixed odd-core/component alternatives.
Source: Aschbacher–Smith, proof of 7.7.3, printed p.707, refs/quasithin.pdf.
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

/-- The actual escaping group cannot have the symmetric-three Thompson
alternative. All subgroups, the full orbit, Q and the reduced quotient remain
those of the original paired-plane construction. -/
theorem sourceOrbit_binary_pairedPlane_thompson_not_symmetricThree
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
              ¬ DoubledBinaryThompsonPlanes.ReducedSymmetricThree (Y.subgroupOf H) hred) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_omega_escape h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let M := normalizer (L : Set G)
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass⟩ := hescape hout
  refine ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,?_⟩
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R ≤ H := le_sup_right.trans hBH
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hQC : Q = (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) := by
    simpa only [D.sourceOrbit_eq] using (D.doubledOrbit_sylow_centralizer h).symm
  have hQR : Q ≤ R := hQC.trans_le (inf_le_inf_left _
    (centralizer_le (ambientPlane_le_orbit D.sourceOrbit E v f)))
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    rw [hQC]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  have heQ : elementaryAbelianMaxJ Q = elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _ hJQ (hQC.trans_le inf_le_left)
  have heR : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _ (hJQ.trans hQR) inf_le_left
  have hBQ : B ≤ normalizer (Q : Set G) := by
    have hcore' : B.pCoreIn 2 = Q := hcore
    rw [← hcore']
    exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hLNJ : localResidual L U ≤ normalizer
      (elementaryAbelianMaxJ ((P : Subgroup H).map H.subtype) : Set G) := by
    rw [hP,heR,← heQ]
    exact (le_sup_left.trans hBQ).trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q)
  have hsupp : U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit := by
    obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
    exact DoubledBinaryOddCore.pairedPlane_residual_supplement
      D.sourceOrbit L hLN q hq E hE v f hfv
  have hBM : B ≤ M := hbase.trans_le (inf_le_left.trans
    (sup_le L.le_normalizer D.sylow_normalizes_component))
  exact DoubledBinaryThompsonPlanes.no_symmetricThree_escape
    H Y D.sourceOrbit U (localResidual L U) B M P hYH hWY
    (le_sup_left.trans hBH) hred
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
    hLNJ hsupp hHC (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le
    hBM hgen hH.1.2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
