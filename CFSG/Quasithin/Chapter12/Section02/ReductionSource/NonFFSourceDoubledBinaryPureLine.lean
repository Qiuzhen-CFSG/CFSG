module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureLine
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryTerminal

/-!
# The original offender's pure commutator line

The full automizer marking carries the actual inner offender four-group to
the concrete natural–dual calculation. Its reverse normalizer hyperplane
has commutator contained in a pure-factor line of order two. The previously
constructed nontrivial shared commutator forces equality with that whole
line. Thus Z₁ is literally [A,A₁], lies in the intersection of the same
noncommuting orbit pair, and belongs to the original seed or its retained
conjugate. Neither factor is identified with the whole orbit W.

The final application supplies an actual pure-line witness whose hyperplane
escapes O₂(C_G(Z₁)). The positive core placement, characteristic-two input
and bound w ≤ 1 still belong to the full non-FF assembly.
Source: Aschbacher–Smith H.4.3(2) and 7.6.1, printed pp.380,702–703,
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The whole commutator of the same offender hyperplanes is an order-two
line in one of the two original marked factors. -/
theorem sourceOrbit_binary_offender_pure_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g) :
    let W := D.sourceOrbit
    let Z := ⁅offenderNormalizer W g,offenderFixedSpan W g⁆
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) ∧
      Z ≤ W ⊓ W.map (MulAut.conj g).toMonoidHom ∧
      W ⊔ W.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) := by
  dsimp only
  let W := D.sourceOrbit
  let A := offenderNormalizer W g
  let B := offenderFixedSpan W g
  let I := inducedAutomizer W A
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  obtain ⟨hI,hIL,_⟩ := D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  let hIE : IsElementaryAbelian 2 I := offender_inducedAutomizer_elementary W g
  have hIc : Nat.card I = 4 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
    change rank I = 2 at hI
    rw [rank,hn,Nat.log_pow (by decide)] at hI
    rw [hn,hI]
    rfl
  obtain ⟨t,ht,hnt,q,hq,E,f,hE,hf,_,_,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let i := W.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.sourceOrbit_component_normalizes)
  have hAI : ∀ a ∈ I, f a ∈ MulAut.innerSubgroup BinaryLinearThree.Group := by
    intro a ha
    obtain ⟨n,hn,he⟩ := hIL ha
    rw [←he]
    exact ⟨q ⟨n,hn⟩,(hf ⟨n,hn⟩).symm⟩
  obtain ⟨P,hP,hmove,haxis⟩ := DoubledBinaryPureLine.four_span_line
    (automizerRepresentation W) i q hq E hE f hf I hAI hIE hIc
  let Q := ambientSubmodule W P
  have hQ : Nat.card Q = 2 := by
    change Nat.card ((moduleSubgroup W P).map W.subtype) = 2
    rw [card_map_of_injective W.subtype_injective]
    exact hP
  have hCQ : ⁅A,B⁆ ≤ Q :=
    DoubledBinaryPureLine.ambient_span_commutator_le W A inf_le_right P hmove
  obtain ⟨Z,hZ,hZC,hZpair,hcentral⟩ :=
    D.sourceOrbit_binary_offender_sharedLine h hd F hF hmodel hnon hw hg
  have he : Z = Q := eq_of_le_of_card_ge (hZC.trans hCQ) (by rw [hQ,hZ])
  have hCZ : ⁅A,B⁆ = Z := le_antisymm (hCQ.trans_eq he.symm) hZC
  have hpure : Q ≤ V ∨ Q ≤ V.map (MulAut.conj t).toMonoidHom := by
    rcases haxis with hn | hd
    · left
      rintro x ⟨v,hv,rfl⟩
      exact (hV (Additive.ofMul v)).mp (hn _ hv)
    · right
      rintro x ⟨v,hv,rfl⟩
      exact (hVt (Additive.ofMul v)).mp (hd _ hv)
  exact ⟨t,ht,hnt,hCZ ▸ hZ,by rwa [hCZ,he],hCZ ▸ hZpair,hCZ ▸ hcentral⟩

/-- The remaining centralizer obstruction uses the literal pure commutator
line of an actual offender, with both original factors retained. -/
theorem sourceOrbit_binary_exists_pureLine_core_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) ∧
        ¬ D.sourceOrbit ≤ (centralizer (Z : Set G)).pCoreIn 2 ∧
        ¬ offenderFixedSpan D.sourceOrbit g ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top D.sourceOrbit_weakClosure_setup
    (ne_top_of_le_ne_top (by simp) hw)
  obtain ⟨t,ht,hnt,hZ,hpure,hpair,hcentral⟩ :=
    D.sourceOrbit_binary_offender_pure_commutator h hd F hF hmodel hnon hw hg
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,
    D.sourceOrbit_binary_not_le_sharedLine_core h hd F hF hmodel hnon hw hg
      (hpair.trans inf_le_left) hZ (hpair.trans inf_le_right),
    fun hcore => D.sourceOrbit_binary_false_of_sharedLine_hyperplane_core
      h hd F hF hmodel hnon hw hg (hpair.trans inf_le_left) hZ (hpair.trans inf_le_right) hcore⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
