module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryLocalCore

/-!
# The original residual/Sylow base in the doubled binary orbit

For the actual paired plane U, L₀ is O²(C_L(U)) and T₀ is C_T(U).
We prove Q = O₂(L₀T₀), with Q = O₂(LT), and retain this exact base
in the minimal escaping SQTK subgroup. The chosen seed and conjugator,
not just an abstract natural–dual module, are retained in both conclusions.

The characteristic-two argument for this H, the needed Sylow arrangement,
and ambient centralizer containment remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith §7.7.2–3, printed pp.704–706, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual original L₀T₀ has precisely the original two-core Q. -/
theorem sourceOrbit_binary_pairedPlane_originalCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          (localBase L (T : Subgroup G) (ambientPlane D.sourceOrbit E v f)).pCoreIn 2 =
            (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,ha,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  exact pairedPlane_localBase_core D.sourceOrbit L T D.sylow_normalizes_component
    D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
    hQ q hq E hE a ha hcov v f hfv

/-- If a paired-plane centralizer escapes, the source base with core Q
lies in an actual minimal escaping SQTK group which does not normalize Q. -/
theorem sourceOrbit_binary_pairedPlane_originalEscape
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
          (localBase L (T : Subgroup G) U).pCoreIn 2 =
            (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar (localBase L (T : Subgroup G) U) (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧
              ¬ H ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,hcore⟩ :=
    D.sourceOrbit_binary_pairedPlane_originalCore h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv
  let U := ambientPlane D.sourceOrbit E v f
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro he
    have hc := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
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
