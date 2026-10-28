module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCharacteristicTwo
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPushingUp
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompson

/-!
# The original escaping group at the start of Thompson factorization

On the same chosen paired plane, retain the complete component and automizer
marking through the established component exclusions and characteristic-two
argument. The whole original doubled orbit lies in the normal closure of
Ω₁(Z(T₀)) under the actual minimal escaping group H. This closure is reduced;
its ambient centralizer is in M, and the actual Thompson image is nontrivial.
B.2.5 and the complete adequate B.5.6 theorem classify that literal image.
The original full Q also satisfies all C.2.3 hypotheses inside H, with its
normal closure formed in H∩M, proving source 7.7.7.

This supplies the opening of the proof of Proposition 7.7.3. Exclusion of the
odd-core and escaping-component alternatives, ambient C_G(U)≤M, and the
final non-FF contradiction remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, printed p.707, refs/quasithin.pdf. The doubled
orbit remains distinct from the chosen seed V, and Q is its full preimage.
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

omit [Finite G] in
private theorem thompson_image_ne_bot (H Y : Subgroup G)
    (hHY : H ≤ normalizer (Y : Set G))
    (hJ : ¬ elementaryAbelianMaxJ H ≤ centralizer (Y : Set G)) :
    inducedAutomizer Y (elementaryAbelianMaxJ H) ≠ ⊥ := by
  intro hz
  apply hJ
  intro j hj
  have hjH : j ∈ H := (show elementaryAbelianMaxJ H ≤ H from
    sSup_le fun _ hA => hA.1) hj
  let n : normalizer (Y : Set G) := ⟨j,hHY hjH⟩
  have hm : Y.normalizerMonoidHom.rangeRestrict n ∈
      inducedAutomizer Y (elementaryAbelianMaxJ H) := ⟨n,hj,rfl⟩
  rw [hz] at hm
  have he := congrArg Subtype.val (mem_bot.mp hm)
  change n ∈ Y.normalizerMonoidHom.ker at he
  rw [normalizerMonoidHom_ker] at he
  exact he

/-- The original doubled orbit lies in the reduced Sylow omega-center orbit
of the actual minimal escaping group. Its centralizer is in M, and its
Thompson subgroup acts nontrivially on that same reduced module. -/
theorem sourceOrbit_binary_pairedPlane_omega_escape
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
              DoubledBinaryThompson.ReducedThompsonAlternative (Y.subgroupOf H) hred) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_constrained_escape_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let M := normalizer (L : Set G)
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf⟩ := hescape hout
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hWR : D.sourceOrbit ≤ R := le_inf D.sourceOrbit_weakClosure_setup.le_sylow
    ((le_centralizer D.sourceOrbit).trans (centralizer_le hUW))
  have hBH : B ≤ H := hH.1.1.2
  have hLH : L ⊓ centralizer (U : Set G) ≤ H := by
    apply le_trans _ hBH
    change L ⊓ centralizer (U : Set G) ≤ localBase L (T : Subgroup G) U
    rw [hbase]
    exact inf_le_inf_right _ le_sup_left
  have hWY : D.sourceOrbit ≤ Y := orbit_le_omegaClosure D.sourceOrbit L R H E hmark
    v f hfv hWR (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans D.sourceOrbit_weakClosure_setup.normalizes) inf_le_right hLH
  have hred : IsPReduced 2 (Y.subgroupOf H) := omegaClosure_reduced H R P hP hchar
  have hQne : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
    intro he
    exact D.sourceOrbit_weakClosure_setup.nontrivial
      (le_bot_iff.mp (he ▸ (D.sourceOrbit_core_normalizer h).1))
  have hpush := DoubledBinaryPushingUp.pairedPlane_pushingUp L U (T : Subgroup G) H
    ((L ⊔ (T : Subgroup G)).pCoreIn 2) P hSQ D.sylow_normalizes_component
    hBH hHC hP hcore hQne (D.sourceOrbit_core_characteristic_control h)
  have hcent : centralizer (Y : Set G) ≤ M := (centralizer_le hWY).trans
    (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le
  have hBM : B ≤ M := hbase.trans_le (inf_le_left.trans
    (sup_le L.le_normalizer D.sylow_normalizes_component))
  have hJ : ¬ elementaryAbelianMaxJ H ≤ centralizer (Y : Set G) := by
    intro hc
    apply hH.1.2
    rw [hgen]
    exact sup_le (hc.trans hcent) hBM
  have hYH : Y ≤ H := conjugateSpanBy_le_self
    (by
      intro z hz
      exact (show R ≤ H from le_sup_right.trans hBH)
        ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hJH : ¬ elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ centralizer (Y.subgroupOf H : Set H) := by
    intro hc
    apply hJ
    have he : elementaryAbelianMaxJ H =
        (elementaryAbelianMaxJ (⊤ : Subgroup H)).map H.subtype := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
        ← MonoidHom.range_eq_map,range_subtype]
    rw [he]
    rintro j ⟨k,hk,rfl⟩ y hy
    exact congrArg Subtype.val (hc hk ⟨y,hYH hy⟩ hy)
  exact ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,hWY,hred,hcent,hJ,
    thompson_image_ne_bot H Y (le_normalizer_conjugateSpanBy _ _) hJ,
    DoubledBinaryThompson.reduced_thompson_adequate _ hred hSQ hJH⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
