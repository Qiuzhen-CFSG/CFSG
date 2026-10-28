module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# E.6.18 using only the original corank-two lifting

The source only invokes component lifting for U and its conjugates when
m(V/U) ≤ 2. Its earlier escape argument first establishes m > 2, and E.6.17
makes the conjugate intersections nonidentity. The narrower lifting contract
therefore suffices for the original normalization and fixed-space contradiction.
Uniqueness is discharged by the proved seven-component rank argument.

This preserves the original SevenLifting API while avoiding its unnecessary
quantification over every corank. The model/containing-component construction
of the narrower lifting remains an explicit earlier input; this module does
not assert a completed model classification.

Source: Aschbacher–Smith, E.6.18, printed p.252.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- The lifting statement only at the coranks used by E.6.18. -/
@[expose] def SevenCorankTwoLifting (V : Subgroup G) : Prop :=
  ∀ A U L : Subgroup G, A ≤ U → U ≤ V → A ≠ ⊥ → subgroupCorank V U ≤ 2 →
    CentralizerComponent U L → IsSeven L → CentralizerComponent A L

omit [Finite G] in
private theorem conjugate_component {U L : Subgroup G}
    (hL : CentralizerComponent U L) (g : G) :
    CentralizerComponent (U.map (MulAut.conj g).toMonoidHom)
      (L.map (MulAut.conj g).toMonoidHom) := by
  have hm := IsComponentIn.map (show IsComponentIn L (centralizer (U : Set G)) from hL)
    (MulAut.conj g)
  rw [Theory.Quasithin.map_centralizer] at hm
  exact hm

/-- The narrower lifting conclusion still supplies exactly the source
normalization argument, including the corank bound for the conjugate. -/
theorem normalizes_component_of_corank_two_lifting [IsElementaryAbelian 2 V]
    (hlift : SevenCorankTwoLifting V) (huniq : SevenUniqueness V)
    {U L : Subgroup G} (hUV : U ≤ V) (hc : subgroupCorank V U ≤ 2)
    (hL : CentralizerComponent U L) (hs : IsSeven L)
    (hdim : 2 * subgroupCorank V U < Module.finrank (ZMod 2) (Additive V)) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  let f := (MulAut.conj g).toMonoidHom
  have hUg : U.map f ≤ V :=
    (map_mono (f := f) hUV).trans (mem_normalizer_iff_map_conj_eq.mp hg).le
  have hne : U ⊓ U.map f ≠ ⊥ := inf_conjugate_ne_bot g hg hdim
  have hfirst := hlift (U ⊓ U.map f) U L inf_le_left hUV hne hc hL hs
  have hsg : IsSeven (L.map f) := hs.of_equiv ((MulAut.conj g).subgroupMap L)
  have hsecond := hlift (U ⊓ U.map f) (U.map f) (L.map f)
    inf_le_right hUg hne (by rwa [corank_conjugate V U g hg])
    (conjugate_component hL g) hsg
  exact mem_normalizer_iff_map_conj_eq.mpr
    (huniq _ (inf_le_left.trans hUV) hne _ _ hfirst hsecond hs hsg).symm

/-- The literal E.6.18 output from lifting only the source coranks, invoked
after the earlier escape theorem has proved m > 2. -/
theorem sevenExcluded_of_corank_two_lifting [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (h15 : HypothesisE615 V) (h8 : SevenEscape M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hlift : 2 < localM V → SevenCorankTwoLifting V) :
    Enlargement.SevenExcluded M V := by
  intro U hU hc L hL hs
  obtain ⟨W, hW, _, hLW⟩ := h8 U hU L hL hs
  have hWescape : ¬ centralizer (W : Set G) ≤ M :=
    fun hC => hLW (inf_le_right.trans hC)
  obtain ⟨hr, hm, _⟩ := lemma_E_6_16_1 h h15 hW hWescape
  have hdim := (lemma_E_6_17 h h15 h13 hr).2
  have hnorm := normalizes_component_of_corank_two_lifting (hlift hm)
    (seven_uniqueness h) hU.1 hc hL hs (by omega)
  let F := V ⊓ centralizer (L : Set G)
  have hUF : U ≤ F := (component_fixedSpace hU.1 hL).1
  have hFc : subgroupCorank V F < localM V :=
    lt_of_le_of_lt (subgroupCorank_antitone hUF) (by omega)
  have hLF : L ≤ centralizer (F : Set G) := le_centralizer_iff.mpr inf_le_right
  have hFescape : ¬ centralizer (F : Set G) ≤ M :=
    fun hC => hLW (inf_le_left.trans (hLF.trans hC))
  have hFG := small_escape_mem h (show F ≤ V from inf_le_left) hFc hFescape
  apply h13 F hFG
  exact (le_inf h.sylow_le_normalizer
    ((h.sylow_le_normalizer.trans hnorm).trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
