module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.LocalFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.BlockRecognition
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter3.Section02
public import Theory.GroupTheory.PCoreImage

/-!
# Excluding S₆ in the initial component argument

The actual isomorphism X* ≃ S₆ gives O^{3′}(Gᵥ) = K and Lᵥ ≤ K.
The central-cover and permutation calculations identify the marked Lᵥ
with A₄. Its two-core and the marked cubic action control [O₂(L),Lᵥ];
normal generation then identifies U(L) with the actual V and constructs
the natural A₅-block module. These steps are supplied by `ResidualA4`
and `BlockRecognition`, including their literal quotient and action maps.

For an actual A₅-block L, full C.1.13(c) gives O₂(LT) = U(L), since the
preceding source inputs give C_T(L) = 1. Its natural-module clause makes
U(L) have order sixteen. The actual marked V has the same order and lies
in O₂(LT), so V = O₂(LT). The proved core-containment form of 3.2.11 now
gives O₂(M) = C_G(V) = V. The actual abelian conjugate span and outside
centralizer contradict this equality.

`SourceData.not_symmetricSix_of_action` assembles this S₆ contradiction;
`not_symmetricSix` also constructs the action data from the source setup.
The genuine preceding local and Fundamental Setup inputs remain in
`SourceData`, and the universal earlier conjugacy and full C.1.13(c)
contracts remain explicit. No A₄ isomorphism, block status or desired
core equality is an input. L₀ = L is proved in `LocalFacts`. The final
consumer removes S₆ from the independent model-sieve alternative.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed p.927; C.1.13(c) and 3.2.11.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open A5Module ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
variable {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

/-- Apply the full earlier block theorem with relative normality and the actual Sylow witness. -/
theorem SourceData.block_conclusions (d : Setup κ T s) {M : Subgroup G}
    (h : SourceData d M) (earlier : EarlierC113c.{u})
    (hb : IsAlternatingBlock L 5) : C113cConclusion L (T : Subgroup G) 5 := by
  apply earlier G L (T : Subgroup G) 5
  · exact (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le L.le_normalizer h.T_normalizes)
  · refine ⟨T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right), ?_⟩
    exact map_subgroupOf_eq_of_le le_sup_right
  · exact hb
  · exact Or.inr rfl

omit [Finite G] in
theorem C113cConclusion.blockU_card {R : Subgroup G}
    (h : C113cConclusion L R 5) : Nat.card ((blockU L).map L.subtype) = 16 := by
  obtain ⟨model⟩ := h.natural
  have hc := Nat.card_congr model.moduleIso.toEquiv
  change Nat.card (blockU L) = Nat.card (BinaryPermutation.natural (Fin 5)) at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := BinaryPermutation.natural (Fin 5)), Nat.card_zmod,
    BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)] at hc
  have he := Nat.card_congr ((blockU L).equivMapOfInjective L.subtype
    L.subtype_injective).toEquiv
  norm_num at hc
  exact he.symm.trans hc

/-- Containment and the two actual natural-module orders force V = O₂(LT). -/
theorem SourceData.core_eq_of_block (d : Setup κ T s) {M : Subgroup G}
    (h : SourceData d M) (earlier : EarlierC113c.{u})
    (hb : IsAlternatingBlock L 5) :
    V = (pCore 2 ↥(L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype := by
  have hout := h.block_conclusions d earlier hb
  have hc := hout.product
  rw [h.centralizer_T d, sup_bot_eq] at hc
  have hVQ : V ≤ (pCore 2 ↥(L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype :=
    h.moduleData.V_le_core.trans (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer h.T_normalizes))
  rw [hc] at hVQ
  have hVU : V = (blockU L).map L.subtype := eq_of_le_of_card_ge hVQ (by
    rw [hout.blockU_card, marking_card s])
  exact hVU.trans hc.symm

/-- The proved 3.2.11 core-sandwich argument supplies both remaining equalities. -/
theorem SourceData.core_recovery_of_block (d : Setup κ T s) {M : Subgroup G}
    (h : SourceData d M) (earlier : EarlierC113c.{u})
    (hb : IsAlternatingBlock L 5) :
    (pCore 2 M).map M.subtype = V ∧
      normalizer (V : Set G) = M ∧ centralizer (V : Set G) = V := by
  let : IsMulCommutative V := marking_commutative s
  have hc := Chapter3.Section02.lemma_3_2_11_of_core_containment T L
    (L ⊔ (T : Subgroup G)) M V le_sup_right (h.LT_le_M d)
    (le_sup_left.trans (h.LT_le_M d)) (h.M_eq_normalizer d) h.maximal h.characteristic_two
    (h.core_eq_of_block d earlier hb) h.moduleData.V_le_core (marking_nontrivial s)
  exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

/-- The abelian span contradicts the resulting self-centralizer. -/
theorem SourceData.contradiction_of_block (d : Setup κ T s) {M : Subgroup G}
    (h : SourceData d M) (earlier : EarlierC113c.{u})
    (hb : IsAlternatingBlock L 5) : False := by
  let := h.abelian_span
  exact not_selfCentralizing_of_abelian_span V M (markedZ s) h.z_outside h.normalizer_V
    (h.core_recovery_of_block d earlier hb).2.2.le

/-- The S₆ branch of 13.6.6 is impossible. The component extraction supplies
the actual A₄ residual, and block recognition supplies its short-group and
natural-module clauses before C.1.13(c) and 3.2.11 are applied. -/
theorem SourceData.not_symmetricSix_of_action (d : Setup κ T s) {M : Subgroup G}
    (h : SourceData d M) (hconj : EarlierConjugates κ) (hblock : EarlierC113c.{u})
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty (XStar K ≃* Equiv.Perm (Fin 6)) := by
  rintro ⟨e₆⟩
  obtain ⟨e₄⟩ := residual_isA4 d h.moduleData hconj hodd K hK a e₆
  have hb := h.isAlternatingBlock_of_residualA4 d hconj hodd K hK e₆ e₄
  exact h.contradiction_of_block d hblock hb

/-- Source-facing S₆ exclusion, with the actual component action constructed
from the preceding setup rather than retained as an additional premise. -/
theorem SourceData.not_symmetricSix (d : Setup κ T s) {M : Subgroup G}
    (h : SourceData d M) (hconj : EarlierConjugates κ) (hblock : EarlierC113c.{u})
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K) :
    ¬ Nonempty (XStar K ≃* Equiv.Perm (Fin 6)) :=
  h.not_symmetricSix_of_action d hconj hblock hodd K hK
    (source_action_data d hconj hodd K hK)

/-- Apply the S₆ exclusion to the literal model-sieve output. The independent
model sieve remains an explicit premise; this theorem retains its original
component image, central four-group and action data in the large-field branch. -/
theorem SourceData.largeField_of_modelSieve (d : Setup κ T s) {M : Subgroup G}
    (h : SourceData d M) (hconj : EarlierConjugates κ) (hblock : EarlierC113c.{u})
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) (hsieve : ModelSieveAlternatives K a) :
    LargeField K a :=
  hsieve.resolve_right (h.not_symmetricSix_of_action d hconj hblock hodd K hK a)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
