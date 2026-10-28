module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPairGeneration
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryThreeOuter

/-!
# Pair generation on the original binary doubled orbit

The original component and whole-automizer marking make every inner
elementary actor quadratic on the literal source orbit W. The proved
equality-case geometry identifies the offender and reverse normalizer
hyperplanes. Inverse conjugation gives the same offender calculation on
the reversed pair, without identifying W with the chosen seed V.

Consequently the product of the two normalizer hyperplanes is a normal
two-subgroup with two central layers. Every odd subgroup of the pair fixes
those layers, then fixes both W and its conjugate; hence their join is a
two-group. The original 7.7.1 theorem supplies r ≥ 3 in the final application.
The still-explicit bound w ≤ 1 remains with the odd-normalizer reduction.
The central line, its local two-core placement, and the Baer–Suzuki endgame
remain with the full non-FF doubled assembly.

Source: Aschbacher–Smith 7.5.3,7.6.1 and 7.7.1,
printed pp.700,702–703, refs/quasithin.pdf.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The natural three-dimensional marking of the literal seed action.
This transparent name shares the dependent action type in the pair-generation
signatures; callers can still supply the original `ActionEquiv` directly. -/
@[expose] def HasNaturalThreeSeed (F : BinaryField) : Prop :=
  Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
    (linearNatural F 3))

/-- Non-FF for the unchanged full source-orbit normalizer action.
The body is exposed so the original non-FF hypothesis is accepted directly. -/
@[expose] def SourceOrbitNonFF : Prop :=
  ¬ IsFFModule D.sourceOrbitNormalizerRepresentation

/-- Every original inner elementary actor acts quadratically on the whole source orbit. -/
theorem sourceOrbit_binary_inner_quadratic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup (Automizer D.sourceOrbit)) [IsElementaryAbelian 2 A]
    (hAL : A ≤ inducedAutomizer D.sourceOrbit L) :
    IsQuadratic (automizerRepresentation D.sourceOrbit) A := by
  obtain ⟨_,_,_,q,hq,E,f,hE,hfL,_,_,_,_⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let i := D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.sourceOrbit_component_normalizes)
  apply doubledBinary_inner_quadratic
    (automizerRepresentation D.sourceOrbit) i q hq E hE f hfL A
  intro a ha
  obtain ⟨n,hn,he⟩ := hAL ha
  rw [←he]
  exact ⟨q ⟨n,hn⟩,(hfL ⟨n,hn⟩).symm⟩

/-- The actual offender commutator centralizes the full conjugate orbit. -/
theorem sourceOrbit_binary_offender_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (hw : globalW D.sourceOrbit T ≤ 1) (hr : 3 ≤ globalR D.sourceOrbit)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g) :
    ⁅D.sourceOrbit,offenderNormalizer D.sourceOrbit g⁆ ≤
      D.sourceOrbit ⊓ centralizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨_,hi,_⟩ := D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  let : IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit
      (offenderNormalizer D.sourceOrbit g)) := offender_inducedAutomizer_elementary _ _
  have hq := D.sourceOrbit_binary_inner_quadratic h hd F hF hmodel _ hi
  have hb := DoubledBinaryPairGeneration.commutator_le_fixed_of_quadratic
    D.sourceOrbit (offenderNormalizer D.sourceOrbit g) inf_le_right hq
  obtain ⟨_,_,hs,_⟩ := D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr
  rwa [(offender_fixedSpaceFamily_of_lt_globalS hg hs).1] at hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem reverse_normalizer_map (W : Subgroup G) (g : G) :
    (offenderNormalizer W g⁻¹).map (MulAut.conj g).toMonoidHom =
      W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hinv : (W.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = W := by
    simpa only [inv_inv] using offender_map_conj_inverse W g⁻¹
  rw [offenderNormalizer, map_inf _ _ _ (MulAut.conj g).injective,
    hinv, map_equiv_normalizer_eq]

omit [Finite G] in
private theorem reverse_offender_at
    {W : Subgroup G} [IsElementaryAbelian 2 W]
    (hw : globalW W T = 1) {g : G} (hg : IsWOffenderAt W T g)
    (hc : subgroupCorank W (W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) = 1) :
    IsWOffenderAt W T g⁻¹ := by
  have hinv : (W.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = W := by
    simpa only [inv_inv] using offender_map_conj_inverse W g⁻¹
  constructor
  · intro he
    have hm := congrArg (fun A : Subgroup G => A.map (MulAut.conj g).toMonoidHom) he
    rw [map_commutator,hinv,Subgroup.map_bot,commutator_comm] at hm
    exact hg.1 hm
  · have he := relIndex_map_map_of_injective
      (offenderNormalizer W g⁻¹) (W.map (MulAut.conj g⁻¹).toMonoidHom)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hinv,reverse_normalizer_map] at he
    rw [hw,subgroupCorank,←he]
    exact_mod_cast hc.symm

/-- Both commutator bounds for the same pair, with the reverse calculation obtained by inverse conjugation. -/
theorem sourceOrbit_binary_offender_pair_commutators
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g) :
    let W := D.sourceOrbit
    let Wg := W.map (MulAut.conj g).toMonoidHom
    ⁅W,offenderNormalizer W g⁆ ≤ W ⊓ centralizer (Wg : Set G) ∧
      ⁅Wg,offenderFixedSpan W g⁆ ≤ Wg ⊓ centralizer (W : Set G) := by
  dsimp only
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  have hf := D.sourceOrbit_binary_offender_commutator h hd F hF hmodel hnon hw hr hg
  obtain ⟨hweq,_,_,_⟩ := D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr
  obtain ⟨_,_,_,hB,_,hcor,_⟩ :=
    D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  have hrev := reverse_offender_at hweq hg (by rwa [←hB])
  have hb := D.sourceOrbit_binary_offender_commutator h hd F hF hmodel hnon hw hr hrev
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hb
  have hinv : (D.sourceOrbit.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = D.sourceOrbit := by
    simpa only [inv_inv] using offender_map_conj_inverse D.sourceOrbit g⁻¹
  rw [map_commutator,reverse_normalizer_map,←hB,
    map_inf _ _ _ (MulAut.conj g).injective,offender_centralizer_map,hinv] at hm
  exact ⟨hf,hm⟩

/-- The original pair centralizes both layers of its normal two-subgroup of hyperplanes. -/
theorem sourceOrbit_binary_offender_pair_series
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g) :
    let W := D.sourceOrbit
    let Wg := W.map (MulAut.conj g).toMonoidHom
    let N := offenderNormalizer W g ⊔ offenderFixedSpan W g
    let Z := (W ⊓ centralizer (Wg : Set G)) ⊔ (Wg ⊓ centralizer (W : Set G))
    let X := W ⊔ Wg
    IsPGroup 2 N ∧ (N.subgroupOf X).Normal ∧
      X ≤ centralizer (Z : Set G) ∧ ⁅X,N⁆ ≤ Z := by
  dsimp only
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  obtain ⟨hf,hrev⟩ := D.sourceOrbit_binary_offender_pair_commutators h hd F hF hmodel hnon hw hg
  obtain ⟨_,_,_,hB,_⟩ := D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  rw [hB] at hrev ⊢
  let : IsElementaryAbelian 2 (D.sourceOrbit.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  exact DoubledBinaryPairGeneration.pair_series _ _ hf hrev

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every odd subgroup of the actual pair centralizes the whole pair; original r ≥ 3 controls both hyperplanes. -/
theorem sourceOrbit_binary_offender_odd_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g)
    (Y : Subgroup G) (hYX : Y ≤ D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom)
    (ho : Odd (Nat.card Y)) :
    Y ≤ centralizer ((D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  let W := D.sourceOrbit
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer W g
  let B := offenderFixedSpan W g
  let Z := (W ⊓ centralizer (Wg : Set G)) ⊔ (Wg ⊓ centralizer (W : Set G))
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  obtain ⟨hweq,_,_,_⟩ := D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr
  obtain ⟨_,_,_,hB,_,hcorB,hiB,_⟩ :=
    D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  obtain ⟨hpN,_,hCZ,hstep⟩ := D.sourceOrbit_binary_offender_pair_series h hd F hF hmodel hnon hw hg
  have hcorA : subgroupCorank Wg A = 1 := by
    have hh := hg.2
    rw [hweq] at hh
    exact_mod_cast hh.symm
  have hiA : A.relIndex Wg = 2 := by
    let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
    rw [subgroupCorank_eq_quotient_finrank] at hcorA
    rw [relIndex_eq_two_pow_quotient_finrank Wg A,hcorA]
    rfl
  have hZN : Z ≤ A ⊔ B := by
    change _ ≤ A ⊔ offenderFixedSpan W g
    change offenderFixedSpan W g = _ at hB
    rw [hB]
    exact sup_le
      ((inf_le_inf_left W (Subgroup.centralizer_le_normalizer _)).trans le_sup_right)
      ((inf_le_inf_left Wg (Subgroup.centralizer_le_normalizer _)).trans le_sup_left)
  have hCB : centralizer (B : Set G) ≤ normalizer (W : Set G) :=
    centralizer_le_normalizer_of_corank_lt_globalR (offenderFixedSpan_le W g)
      (by rw [hcorB]; exact lt_of_lt_of_le (by decide) hr)
  have hCA : centralizer (A : Set G) ≤ normalizer (Wg : Set G) :=
    centralizer_le_normalizer_of_corank_lt_globalR (show A ≤ Wg from inf_le_left)
      (by rw [hcorA,globalR_map_equiv]; exact lt_of_lt_of_le (by decide) hr)
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  exact DoubledBinaryPairGeneration.odd_pair_centralizes W Wg A B Z Y inf_le_left
    (offenderFixedSpan_le W g) hiA hiB hCZ hstep hZN hpN hCB hCA hYX ho

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The source equality-case conjugate pair generates a two-group. -/
theorem sourceOrbit_binary_offender_pair_isPGroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g) :
    IsPGroup 2 (D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  apply DoubledBinaryPairGeneration.pair_isPGroup_of_odd_centralizes _ _
    (IsElementaryAbelian.isPGroup 2 _) ((IsElementaryAbelian.isPGroup 2 D.sourceOrbit).map _)
  intro Y hYX ho
  exact D.sourceOrbit_binary_offender_odd_centralizes h hd F hF hmodel hnon hw hg Y hYX ho

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
