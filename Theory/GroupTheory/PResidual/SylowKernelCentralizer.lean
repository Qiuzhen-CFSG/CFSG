module
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.SylowLocalCore

/-!
# The Sylow-supplement core centralizes a normal kernel modulo O₂

Let C be normal in a finite group H with T∩C=O₂(H). Set X=O²(C) and
R=O₂(XT). The Sylow supplement theorem gives C≤XT. Hence [C,R] lies
in C∩R≤C∩T=O₂(H). The same construction contains O₂(H), so R∩C is
exactly O₂(H). This supplies the actual centralizer in the E.2.1 escape.

Source: Aschbacher–Smith 13.2.9, printed pp. 880–881.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem residual_sylow_core_centralizes (T : Sylow 2 G) (C : Subgroup G) [C.Normal]
    (hTC : (T : Subgroup G) ⊓ C = pCore 2 G) :
    let X := (pResidual 2 C).map C.subtype
    let R := (X ⊔ (T : Subgroup G)).pCoreIn 2
    pCore 2 G ≤ R ∧ R ≤ (T : Subgroup G) ∧ R ⊓ C = pCore 2 G ∧
      R ≤ centralizerModulo (T : Subgroup G) C (pCore 2 G) := by
  let X := (pResidual 2 C).map C.subtype
  let Y := X ⊔ (T : Subgroup G)
  let R := Y.pCoreIn 2
  have hCY : C ≤ Y := le_embedded_pResidual_sup_sylow_of_normalizes T C le_normalizer_of_normal
  have hQT : pCore 2 G ≤ (T : Subgroup G) := pCore_isPGroup.le_sylow_of_normal T
  have hQR : pCore 2 G ≤ R := le_pCoreIn_of_normalizes pCore_isPGroup
    (hQT.trans le_sup_right) le_normalizer_of_normal
  have hRT : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow Y (T.subtype (show (T : Subgroup G) ≤ Y from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ Y from le_sup_right)] using hh
  have hRC : R ⊓ C = pCore 2 G := le_antisymm
    ((inf_le_inf_right _ hRT).trans_eq hTC) (le_inf hQR (hTC.ge.trans inf_le_right))
  have hnR : C ≤ normalizer (R : Set G) := (hCY.trans Y.le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hc : ⁅C,R⁆ ≤ pCore 2 G := by
    rw [←hRC]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp hnR) (commutator_le_left _ _)
  refine ⟨hQR,hRT,hRC,?_⟩
  intro r hr
  exact mem_centralizerModulo_iff.mpr ⟨hRT hr,fun c hcC => hc (commutator_mem_commutator hcC hr)⟩
end Subgroup

