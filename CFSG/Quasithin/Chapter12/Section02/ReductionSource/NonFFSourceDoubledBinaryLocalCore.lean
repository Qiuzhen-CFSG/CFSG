module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlaneQuotient

/-!
# The original doubled-orbit local core and escaping subgroup

For each paired plane U, the literal C_{LT}(U) has two-core
Q = O₂(LT) = C_T(W). Normalizer uniqueness controls N_G(Q).
If C_G(U) escapes M, finite descent supplies a minimal escaping H over
the original O²(C_L(U))C_T(U), with U ≤ O₂(H), genuine SQTK hypotheses,
and failure to normalize Q. The original seed and conjugator are retained.

These are local inputs to 7.7.3–6. They do not identify C_{LT}(U) with
L₀T₀, prove the required Sylow arrangement, establish characteristic two
for H, or prove ambient centralizer containment. Those arguments and
final non-FF assembly remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, printed pp.704–706, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryPlaneQuotient DoubledBinaryLocalCore
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual orbit lies in Q, and the original local uniqueness controls N_G(Q). -/
theorem sourceOrbit_core_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    D.sourceOrbit ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) := by
  have hWQ : D.sourceOrbit ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← D.doubledOrbit_sylow_centralizer h,← D.sourceOrbit_eq]
    exact le_inf D.sourceOrbit_weakClosure_setup.le_sylow (le_centralizer D.sourceOrbit)
  refine ⟨hWQ,D.normal_subgroup_normalizer_le h.toHypothesis1221
    (pCoreIn_le 2 _) ?_ ?_⟩
  · intro he
    exact D.sourceOrbit_weakClosure_setup.nontrivial (le_bot_iff.mp (he ▸ hWQ))
  · exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The full local centralizer preimage has exactly the original two-core. -/
theorem sourceOrbit_binary_pairedPlane_localCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          ((L ⊔ (T : Subgroup G)) ⊓
            centralizer (ambientPlane D.sourceOrbit E v f : Set G)).pCoreIn 2 =
              (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,ha,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
    rw [← D.doubledOrbit_sylow_centralizer h,← D.sourceOrbit_eq]
    exact inf_le_right
  exact pairedPlane_core D.sourceOrbit L (L ⊔ (T : Subgroup G))
    D.sourceOrbit_component_normalizes le_sup_left
    (sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes)
    hQ q hq E hE a ha hcov v f hfv

/-- The paired-plane core and original minimal escaping SQTK group,
under the contrary ambient-containment assumption. -/
theorem sourceOrbit_binary_pairedPlane_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          let U := ambientPlane D.sourceOrbit E v f
          ((L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G)).pCoreIn 2 =
            (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar (localBase L (T : Subgroup G) U) (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧
              ¬ H ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,hcore⟩ :=
    D.sourceOrbit_binary_pairedPlane_localCore h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv
  let U := ambientPlane D.sourceOrbit E v f
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro he
    have hc := ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hc
    rw [he,Subgroup.card_bot] at hc
    omega
  have hUC : U ≤ centralizer (U : Set G) :=
    (hUW.trans (le_centralizer D.sourceOrbit)).trans (centralizer_le hUW)
  have hUB : U ≤ localBase L (T : Subgroup G) U :=
    (le_inf (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow) hUC).trans le_sup_right
  have hBC : localBase L (T : Subgroup G) U ≤ centralizer (U : Set G) :=
    sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  refine ⟨hcore v f hfv,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ⟩ := minimal_escape h.simpleQTKE U
    (localBase L (T : Subgroup G) U) (normalizer (L : Set G)) hp hU hUB hBC hout
  refine ⟨H,hH,hHC,hUH,hSQ,?_⟩
  intro hHQ
  exact hH.1.2 (hHQ.trans (D.sourceOrbit_core_normalizer h).2)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
