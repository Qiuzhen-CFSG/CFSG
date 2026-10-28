module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Characteristic
public import Theory.GroupTheory.ElementaryThompsonComponent
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The final Thompson contradiction after 13.6.23

If T normalizes X, the index-two centralizer Tᵥ is also T-invariant, so
T acts on Rᵥ = O₂(XTᵥ). The model equality J(Rᵥ) = J(O₂(KTᵥ)) makes K
normalize the same Thompson subgroup. It is therefore normal in ⟨K,T⟩.
The nonidentity element v lies in Rᵥ, proving J(Rᵥ) is nontrivial; this
contradicts the earlier two-core vanishing in 13.6.16(1).

The specific orthogonal-module Thompson equality is still an input. This
file proves the normality, containment and nontriviality steps; it does not
assert the model classification or any conclusion of 13.6.23.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.933,
concluding paragraph of the proof of Theorem 13.6.7.
-/

@[expose] public section
open Subgroup Stellmacher
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_J (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (elementaryAbelianMaxJ H : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change H.map (MulAut.conj g).toMonoidHom = H at hg
  change (elementaryAbelianMaxJ H).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv, hg]

omit [Finite G] in
private theorem J_le (H : Subgroup G) : elementaryAbelianMaxJ H ≤ H :=
  sSup_le fun _ hA => hA.1

/-- The B.3.2.4 Thompson comparison forces a nontrivial normal two-subgroup
of ⟨K,T⟩, contradicting 13.6.16(1). No normal Thompson subgroup or
containment in the vanishing two-core is assumed. -/
theorem false_of_orthogonal_thompson_comparison (T : Sylow 2 G) (v : G) (K X : Subgroup G)
    (hvT : v ∈ T) (hv : v ≠ 1) (hXv : X ≤ Gv v)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hJ : elementaryAbelianMaxJ ((X ⊔ Tv (T : Subgroup G) v).pCoreIn 2) =
      elementaryAbelianMaxJ ((K ⊔ Tv (T : Subgroup G) v).pCoreIn 2))
    (h16 : (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥) : False := by
  let C := Tv (T : Subgroup G) v
  let R := (X ⊔ C).pCoreIn 2
  let Q := (K ⊔ C).pCoreIn 2
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show C ≤ (T : Subgroup G) from inf_le_left)).mp (normal_of_index_eq_two hidx)
  have hTH : (T : Subgroup G) ≤ normalizer ((X ⊔ C : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hTX ht),
      mem_normalizer_iff_map_conj_eq.mp (hTC ht)]
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    hTH.trans (normalizer_le_normalizer_characteristic_image (X ⊔ C) (pCore 2 (X ⊔ C : Subgroup G)))
  have hKQ : K ≤ normalizer (Q : Set G) :=
    (le_sup_left.trans (K ⊔ C).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ C) (pCore 2 (K ⊔ C : Subgroup G)))
  have hKJ : K ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
    rw [hJ]
    exact hKQ.trans (normalizes_J Q)
  have hnorm : K ⊔ (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ R : Set G) :=
    sup_le hKJ (hTR.trans (normalizes_J R))
  have hle : elementaryAbelianMaxJ R ≤ K ⊔ (T : Subgroup G) := by
    rw [hJ]
    exact (J_le Q).trans ((pCoreIn_le 2 (K ⊔ C)).trans (sup_le_sup_left inf_le_left K))
  have hbot : elementaryAbelianMaxJ R = ⊥ := by
    apply bot_unique
    rw [← h16]
    exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 (X ⊔ C)).to_le (J_le R)) hle hnorm
  have hvC : v ∈ C := ⟨hvT, mem_centralizer_singleton_iff.mpr rfl⟩
  have hZv : zpowers v ≤ R := by
    apply le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (zpowers_le.mpr hvT))
      (zpowers_le.mpr ((show C ≤ X ⊔ C from le_sup_right) hvC))
    have hcent : X ⊔ C ≤ centralizer (zpowers v : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
      exact sup_le hXv inf_le_right
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hR : R ≠ ⊥ := by
    intro heq
    exact hv (mem_bot.mp (heq ▸ hZv (mem_zpowers v)))
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  have hnon := elementaryAbelianMaxJ_top_ne_bot_of_isPGroup (isPGroup_pCoreIn 2 (X ⊔ C))
  have hm : (elementaryAbelianMaxJ (⊤ : Subgroup R)).map R.subtype =
      elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective]
    rw [← MonoidHom.range_eq_map, R.range_subtype]
  exact hnon ((map_eq_bot_iff_of_injective _ R.subtype_injective).mp (hm.trans hbot))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
