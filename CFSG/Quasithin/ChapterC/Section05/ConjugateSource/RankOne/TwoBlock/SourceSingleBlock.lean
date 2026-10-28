module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.SourceSylow
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoreIdentification
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SingleBlockTerminal
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.SingleBlockFrattini

/-!
# The single-block terminal source identities

The common-normal obstruction kills the actual Φ(D). The original quotient
supplies its Sylow, and the source index-two subgroup forces x² to normalize
K and U. The full core equality and both full-R centralizer products follow
with all auxiliary premises discharged on the literal source subgroups.

Import this consumer from the main C.5 umbrella: its Frattini producer imports
the earlier RankOne umbrella. Source: C.5.6(7)(i), printed pp.159–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.source_single_block_terminal
    (h : Setup R K F) (hR : IsPGroup 2 R)
    (H M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G)) (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) → M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    let C := R ⊓ centralizer (K : Set G)
    K.pCoreIn 2 = U K ∧ R ⊓ centralizer (U K : Set G) = U K ⊔ C ∧
      C ≤ centralizer (V : Set G) ∧ R ⊓ centralizer (V : Set G) = V ⊔ C := by
  have hphi := h.frattini_eq_bot_of_index_two H M T_H hTHM hMR hTHK hH hno hindex x hx hnc
  have hsquare : (U K).conjBy (x^2) = U K := by
    have hs : x^2 ∈ T_H := (T_H.subgroupOf M).sq_mem_of_index_two hindex (⟨x,hx⟩ : M)
    exact mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_characteristic_image K (blockU K) (hTHK hs))
  exact ⟨h.core_eq_module_of_sylow (hMR hx) hnc hphi (h.source_sylow_join hR),
    h.single_block_full_centralizer_products hR (fun _ => h.source_sylow_block hR)
      (hRTH.trans hTHK) (hMR hx) hnc hsquare⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
