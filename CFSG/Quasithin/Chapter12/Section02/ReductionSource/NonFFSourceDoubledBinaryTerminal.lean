module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTerminal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPairGeneration

/-!
# Relative Baer--Suzuki on the original binary doubled orbit

The genuine non-FF Thompson control puts O₂(C_G(Z)) in N_G(W) for every
Z ≤ W, where W is the whole source orbit. For a shared involution line,
source fusion and positive weak closure show that W escapes this core.
If a hyperplane of W lies in the core, each noncommuting local conjugate
has a normalizing hyperplane of index two. It is an actual offender, so
the proved pair-generation theorem and relative Baer--Suzuki force W
into the core, giving the terminal contradiction.

The existing fixed-space dimensions also give a nontrivial commutator of
the two normalizer hyperplanes. An involution in it supplies an actual
shared central line, and hence a witness to failure of hyperplane core
containment. This does not identify that line with the pure-factor line
in H.4.3 or prove the missing core containment. Those geometric steps,
the bound w ≤ 1 and the remaining doubled rows stay with the full non-FF
assembly. The original seed V is never identified with W.

Source: Aschbacher--Smith 3.2.10(2,3,6,8), 7.5.3 and 7.6.1,
printed pp.583--584,700,702--703, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every subgroup of the original orbit has centralizer two-core normalizing that orbit. -/
theorem sourceOrbit_nonFF_subgroup_centralizer_core_normalizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : D.SourceOrbitNonFF) {Z : Subgroup G} (hZW : Z ≤ D.sourceOrbit) :
    (centralizer (Z : Set G)).pCoreIn 2 ≤ normalizer (D.sourceOrbit : Set G) := by
  rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
  exact DoubledBinaryTerminal.centralizer_core_le_of_thompson
    D.sourceOrbit (normalizer (L : Set G)) T
    (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
    (fun R hp hJR => ((D.sourceOrbit_nonFF_thompson_normalizers h hnon).2 R hp hJR).2) hZW

/-- Original full-orbit fusion replaces a conjugator through a shared line by an element of its centralizer. -/
theorem sourceOrbit_nonFF_line_conjugate_through
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : D.SourceOrbitNonFF) {Z : Subgroup G} (hZW : Z ≤ D.sourceOrbit)
    (hZ : Nat.card Z = 2) (g : G)
    (hZg : Z ≤ D.sourceOrbit.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ centralizer (Z : Set G),
      D.sourceOrbit.map (MulAut.conj c).toMonoidHom =
        D.sourceOrbit.map (MulAut.conj g).toMonoidHom := by
  exact DoubledBinaryTerminal.line_conjugate_through
    D.sourceOrbit (normalizer (L : Set G)) T
    (by rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd])
    (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
    (D.sourceOrbit_nonFF_thompson_normalizers h hnon).1 hZW hZ g hZg

/-- Original 3.2.10(6) for the binary equality-case pair: the full orbit escapes
 the centralizer core of every line shared with its noncommuting conjugate. -/
theorem sourceOrbit_binary_not_le_sharedLine_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g)
    {Z : Subgroup G} (hZW : Z ≤ D.sourceOrbit) (hZ : Nat.card Z = 2)
    (hZg : Z ≤ D.sourceOrbit.map (MulAut.conj g).toMonoidHom) :
    ¬ D.sourceOrbit ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  intro hcore
  let C := centralizer (Z : Set G)
  obtain ⟨c,hc,he⟩ := D.sourceOrbit_nonFF_line_conjugate_through h hd hnon hZW hZ g hZg
  have hn : C ≤ normalizer (C.pCoreIn 2 : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hfix : (C.pCoreIn 2).map (MulAut.conj c).toMonoidHom = C.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hn hc)
  have hmap := map_mono (f := (MulAut.conj c).toMonoidHom) hcore
  rw [he,hfix] at hmap
  have hnormal := hmap.trans (D.sourceOrbit_nonFF_subgroup_centralizer_core_normalizes h hd hnon hZW)
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  have hweq := (D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr).1
  have hp : 0 < globalW D.sourceOrbit T := by rw [hweq]; decide
  have hcomm := ((lemma_E_3_25 D.sourceOrbit_weakClosure_setup hp g).1.mp hnormal)
  exact hg.1 (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcomm))

/-- Pair generation and relative Baer--Suzuki absorb the whole orbit once
 one of its hyperplanes lies in the centralizer core. -/
theorem sourceOrbit_binary_le_centralizer_core_of_hyperplane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1)
    {Z A : Subgroup G} (hZW : Z ≤ D.sourceOrbit) (hAW : A ≤ D.sourceOrbit)
    (hi : A.relIndex D.sourceOrbit = 2)
    (hAcore : A ≤ (centralizer (Z : Set G)).pCoreIn 2) :
    D.sourceOrbit ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  by_contra hcore
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  have hweq := (D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr).1
  have hnorm := D.sourceOrbit_nonFF_subgroup_centralizer_core_normalizes h hd hnon hZW
  have hWC : D.sourceOrbit ≤ centralizer (Z : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative D.sourceOrbit)).trans
      (centralizer_le hZW)
  apply Section06To07.false_of_hyperplane_pair_generation Z D.sourceOrbit A
    (IsElementaryAbelian.isPGroup 2 _) hWC hAW hAcore hi hcore
  intro g hg hgindex hgnon
  let B := D.sourceOrbit.map (MulAut.conj g).toMonoidHom ⊓ (centralizer (Z : Set G)).pCoreIn 2
  have hBi : B.relIndex (D.sourceOrbit.map (MulAut.conj g).toMonoidHom) = 2 := by
    rw [inf_relIndex_left]
    exact hgindex
  have hcomm : ⁅D.sourceOrbit,D.sourceOrbit.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hgnon (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  have hoff := DoubledBinaryTerminal.isWOffenderAt_of_normalizing_hyperplane
    D.sourceOrbit_weakClosure_setup hweq (lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3) hr)
    g B inf_le_left (inf_le_right.trans hnorm) hBi hcomm
  exact D.sourceOrbit_binary_offender_pair_isPGroup h hd F hF hmodel hnon hw hoff

/-- The literal final binary contradiction, with only the shared-line geometry
 and its hyperplane placement still to be constructed. -/
theorem sourceOrbit_binary_false_of_sharedLine_hyperplane_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g)
    {Z : Subgroup G} (hZW : Z ≤ D.sourceOrbit) (hZ : Nat.card Z = 2)
    (hZg : Z ≤ D.sourceOrbit.map (MulAut.conj g).toMonoidHom)
    (hAcore : offenderFixedSpan D.sourceOrbit g ≤ (centralizer (Z : Set G)).pCoreIn 2) : False := by
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  obtain ⟨_,_,_,_,_,_,hi,_⟩ := D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  exact D.sourceOrbit_binary_not_le_sharedLine_core h hd F hF hmodel hnon hw hg hZW hZ hZg
    (D.sourceOrbit_binary_le_centralizer_core_of_hyperplane h hd F hF hmodel hnon hw hZW
      (offenderFixedSpan_le D.sourceOrbit g) hi hAcore)

/-- The actual pair has a central involution line in its two normalizer
 hyperplanes' commutator. No equality with a prescribed coordinate line is assumed. -/
theorem sourceOrbit_binary_offender_sharedLine
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g) :
    ∃ Z : Subgroup G, Nat.card Z = 2 ∧
      Z ≤ ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆ ∧
      Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
      D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) := by
  let W := D.sourceOrbit
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer W g
  let B := offenderFixedSpan W g
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  obtain ⟨_,_,hfix,_,_,_,_,hrank⟩ :=
    D.sourceOrbit_binary_offender_geometry h hd F hF hmodel hnon hw hr hg
  obtain ⟨hf,hrev⟩ := D.sourceOrbit_binary_offender_pair_commutators h hd F hF hmodel hnon hw hg
  have hBW : B ≤ W := offenderFixedSpan_le W g
  have hAWg : A ≤ Wg := inf_le_left
  have hcommW : ⁅A,B⁆ ≤ W := by
    rw [commutator_comm]
    exact ((commutator_mono hBW le_rfl).trans hf).trans inf_le_left
  have hcommWg : ⁅A,B⁆ ≤ Wg :=
    ((commutator_mono hAWg le_rfl).trans hrev).trans inf_le_left
  have hne : ⁅A,B⁆ ≠ ⊥ := by
    intro he
    have hBC : B ≤ centralizer (A : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hBU : B ≤ W ⊓ centralizer (A : Set G) := le_inf hBW hBC
    have hcard := Nat.card_le_card_of_injective (inclusion hBU) (inclusion_injective hBU)
    have hlo := Nat.log_mono_right (b := 2) hcard
    change rank B ≤ Nat.log 2 (Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G)) at hlo
    change rank B = 5 at hrank
    change Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) = 8 at hfix
    rw [hrank,hfix] at hlo
    norm_num at hlo
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hzW := hcommW z.property
  have ho : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z : G) hzW) hz1
  let Z := zpowers (z : G)
  have hZcomm : Z ≤ ⁅A,B⁆ := zpowers_le.mpr z.property
  have hZW := hZcomm.trans hcommW
  have hZg := hZcomm.trans hcommWg
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  have hWC : W ≤ centralizer (Z : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative W)).trans
      (centralizer_le hZW)
  have hgC : Wg ≤ centralizer (Z : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative Wg)).trans
      (centralizer_le hZg)
  exact ⟨Z,(Nat.card_zpowers (z : G)).trans ho,hZcomm,le_inf hZW hZg,sup_le hWC hgC⟩

/-- An actual offender and shared central line for which the reverse hyperplane
 escapes the full centralizer two-core. This is the remaining geometric obstruction
 after pair generation and Baer--Suzuki, under the still-explicit upper w bound. -/
theorem sourceOrbit_binary_exists_sharedLine_core_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ Z : Subgroup G, Nat.card Z = 2 ∧
        Z ≤ ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆ ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) ∧
        ¬ D.sourceOrbit ≤ (centralizer (Z : Set G)).pCoreIn 2 ∧
        ¬ offenderFixedSpan D.sourceOrbit g ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top D.sourceOrbit_weakClosure_setup
    (ne_top_of_le_ne_top (by simp) hw)
  obtain ⟨Z,hZ,hZcomm,hZpair,hcentral⟩ :=
    D.sourceOrbit_binary_offender_sharedLine h hd F hF hmodel hnon hw hg
  have hZW := hZpair.trans inf_le_left
  have hZg := hZpair.trans inf_le_right
  exact ⟨g,hg,Z,hZ,hZcomm,hZpair,hcentral,
    D.sourceOrbit_binary_not_le_sharedLine_core h hd F hF hmodel hnon hw hg hZW hZ hZg,
    fun hcore => D.sourceOrbit_binary_false_of_sharedLine_hyperplane_core
      h hd F hF hmodel hnon hw hg hZW hZ hZg hcore⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
