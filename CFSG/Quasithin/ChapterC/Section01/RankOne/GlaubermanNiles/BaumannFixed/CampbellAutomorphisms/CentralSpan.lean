module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.Source
public import Theory.Frattini.ConjugateSpan

/-!
# The central Frattini bound entering Campbell's automorphism argument

For the actual transferred F′ outside F with V′≤O₂(H), put
W=⟨F′^J(H)⟩ and Z′=C_V′(S′), preserving the common Thompson marking.
The comparison theorem makes Z′ central in J(H). The exact core
commutator [J(O₂(H)),F′]=Z′ then propagates to [W,J(O₂(H))]≤Z′.
Consequently W≤J(O₂(H)) and Φ(W)≤Z′. This supplies the genuine
central Frattini layer used in Campbell's involution argument.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.6.1,
printed p.29, following Theorem B; Aschbacher–Smith C.1.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {J H H' : Type*} [Group J] [Group H] [Finite H] [Group H'] [Finite H']
  {B B' : Type*} [Group B] [Finite B] [Group B'] [Finite B']
  {e : B →* H} {e' : B' →* H'}
  {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

theorem InLocalClass.paired_span_core_frattini (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (hF : ¬ d.transfer d' (Campbell.F H') ≤ Campbell.F H) :
    let Y := d.transfer d' (Campbell.F H')
    let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
    let W := conjugateSpanBy Y (Campbell.J (⊤ : Subgroup H))
    W ≤ Campbell.J (pCore 2 H) ∧ ⁅W,Campbell.J (pCore 2 H)⁆ ≤ Z ∧
      (frattini W).map W.subtype ≤ Z := by
  let R := Campbell.J (pCore 2 H)
  let K := Campbell.J (⊤ : Subgroup H)
  let Y := d.transfer d' (Campbell.F H')
  let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
  let W := conjugateSpanBy Y K
  have hYQ := h.transferred_campbellF_le_core hB m h' hB' m' d d' hV
  obtain ⟨A,hA,hYA⟩ := h'.campbellF_le_some_maxElementary hB' d'
  have hYA' : Y ≤ d.transfer d' A := map_mono (comap_mono hYA)
  let : IsElementaryAbelian 2 (d.transfer d' A) := (d.transfer_maxElementary d' A hA).2.1
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYA'
  have hYR : Y ≤ R := h.submaximal_core_le_thompson hB d _ _
    (d.transfer_maxElementary d' A hA) hYA' hYQ
  let : R.Normal := Campbell.core_thompson_normal
  have hWR : W ≤ R := conjugateSpanBy_le hYR le_normalizer_of_normal
  have hZK : Z ≤ centralizer (K : Set H) := h.paired_comparison_centrality hB m h' hB' m' d d' hS hS' hV hF
  have hRZ : R ≤ centralizer (Z : Set H) :=
    (sSup_le fun A hA => le_sSup (d.core_maxFamily_subset_of_fixedIndex (h.omegaFixedIndexBound hB d) hA)).trans
      (le_centralizer_iff.mp (d.transferred_fixed_centralizes_thompson d'))
  have hYRZ : ⁅Y,R⁆ ≤ Z := by rw [commutator_comm]; exact (h.paired_core_commutator hB m h' hB' m' d d' hS' hV hF).le
  let D := commutatorPreimage R R Z
  have hWD : W ≤ D := conjugateSpanBy_le (le_commutatorPreimage hYR hYRZ)
    (commutatorPreimage_normalized R R Z K (hRZ.trans (Subgroup.centralizer_le_normalizer _))
      le_normalizer_of_normal le_normalizer_of_normal
      ((le_centralizer_iff.mp hZK).trans (Subgroup.centralizer_le_normalizer _)))
  have hcomm : ⁅W,R⁆ ≤ Z := (commutator_mono hWD le_rfl).trans
    (commutator_commutatorPreimage_le R R Z (hRZ.trans (Subgroup.centralizer_le_normalizer _)))
  have hWQ : W ≤ pCore 2 H := hWR.trans (sSup_le fun _ hA => hA.1)
  have hWp : IsPGroup 2 W := pCore_isPGroup.of_injective (inclusion hWQ) (inclusion_injective hWQ)
  exact ⟨hWR,hcomm,Subgroup.frattini_conjugateSpan_le_of_commutator Y K Z hWp ((commutator_mono le_rfl hWR).trans hcomm)⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
