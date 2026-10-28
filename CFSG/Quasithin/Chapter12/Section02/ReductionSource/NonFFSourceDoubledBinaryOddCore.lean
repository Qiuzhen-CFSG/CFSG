module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinarySylow
/-!
# The odd core of the actual paired-plane centralizer overgroups

Retain the original seed conjugator and both axes, and select the paired
plane U with C_T(U) Sylow in C_G(U). The local base B=L₀T₀ has core Q,
so it contains the entire orbit W. Its original residual supplies
W=U[W,L₀]. Every B≤H≤C_G(U) inherits SQTK from N_G(U), and H∩M has
characteristic two by the source even-characteristic hypothesis.

A.1.26 now centralizes O(H) on [W,L₀]; centrality on U implies centrality
on W. Hence O(H) lies in M and is trivial. The final clause applies this
to the minimal escaping H. This discharges the odd-core paragraph of
7.7.6, not its ordinary-component elimination or final constrainedness.
All remaining binary and nonbinary branches stay with the final owner
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, original 7.7.6, printed p.705, refs/quasithin.pdf.
-/

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore DoubledBinarySylow
open DoubledBinaryOddCore
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- On a Sylow-placed plane in the original doubled orbit, every overgroup
of the local base in the plane centralizer has trivial odd core. In particular
this eliminates the odd core of the actual minimal escaping SQTK subgroup. -/
theorem sourceOrbit_binary_pairedPlane_oddCore_escape
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
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) → pPrimeCore 2 H = ⊥) ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar B (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧ pPrimeCore 2 H = ⊥) := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,ha,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hMW : M ≤ normalizer (D.sourceOrbit : Set G) :=
    (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
  have hJ := D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon
  have hNJ := (D.sourceOrbit_nonFF_thompson_normalizers h hnon).1
  obtain ⟨v,f,hfv,S,hS⟩ := exists_pairedPlane_sylow D.sourceOrbit M T hTM hMW hJ hNJ E a hcov
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hcore : B.pCoreIn 2 = Q := pairedPlane_localBase_core D.sourceOrbit L T
    D.sylow_normalizes_component D.sourceOrbit_component_normalizes
    D.sourceOrbit_weakClosure_setup.normalizes hQ q hq E hE a ha hcov v f hfv
  have hbase : B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) :=
    localBase_eq_centralizer L U T D.sylow_normalizes_component S hS
  have hgen : U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit :=
    pairedPlane_residual_supplement D.sourceOrbit L D.sourceOrbit_component_normalizes q hq E hE v f hfv
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hWQ : D.sourceOrbit ≤ Q := (D.sourceOrbit_core_normalizer h).1
  have hQB : Q ≤ B := hcore ▸ pCoreIn_le 2 B
  have hUB : U ≤ B := hUW.trans (hWQ.trans hQB)
  have hBC : B ≤ centralizer (U : Set G) := hbase.trans_le inf_le_right
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro hz
    have hc := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hc
    rw [hz,Subgroup.card_bot] at hc
    omega
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  have hodd (H : Subgroup G) (hBH : B ≤ H) (hHC : H ≤ centralizer (U : Set G)) :
      pPrimeCore 2 H = ⊥ := by
    have hQH : Q ≤ H := hQB.trans hBH
    have hMQ : M.pCoreIn 2 ≤ Q := core_le_of_sylow_base (T.subtype hTM)
      (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]; exact le_sup_right)
      (sup_le L.le_normalizer hTM)
    have hMHne : H ⊓ M ≠ ⊥ := by
      intro hz
      have hUM : U ≤ M := (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans hTM
      exact hU (le_bot_iff.mp (hz ▸ le_inf (hUB.trans hBH) hUM))
    have hMH : H ⊓ M ∈ Chapter1.He G := Chapter1.lemma_1_1_4_5 T
      (h.simpleQTKE.evenCharacteristic T) h61.maximalTwoLocal hTM hMHne inf_le_right
      (inf_le_left.trans (le_inf (hMQ.trans hQH) (pCoreIn_le 2 M)))
    have hHN : H ≤ normalizer (U : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
    have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
      ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
    have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
      (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
    exact oddCore_eq_bot_of_residual_supplement D.sourceOrbit U (localResidual L U) H M
      (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
      ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
      (hWQ.trans hQH) (le_sup_left.trans hBH) hgen hHC h61.centralizer_le
      hSQ.stronglyQuasithin (Chapter1.mem_He_iff.mp hMH)
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,⟨S,hS⟩,hbase,hcore,hgen,hodd,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ⟩ := minimal_escape h.simpleQTKE U B M hp hU hUB hBC hout
  exact ⟨H,hH,hHC,hUH,hSQ,hodd H hH.1.1.2 hHC⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
