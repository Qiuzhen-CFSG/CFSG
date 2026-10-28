module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.HeadFamily
public import Theory.SpecificGroups.Triality.TwoLocalCover


/-!
# A counterexample to the proposed head-intersection normalizer criterion

In the genuine binary carrier, let A be the literal head (t,0,0;u,v) and
Q its simple short-root subgroup (t,0,0;0,0). Thus |Q| = q³ > q² and
Q < A. The highest-root reflection, the relative Weyl word sr(3), centralizes
Q. It lies outside the central full parabolic by Bruhat cell separation.
It also cannot normalize A: A contains the highest positive root element,
and the rank-one word would then put this reflection in A ≤ U.

The head is abelian, so it normalizes Q. The model two-core is trivial by the
proved two-local cover; consequently the literal source tau also centralizes
Q. These facts disprove the proposed alternative for every positive binary
exponent, including f = 1, in the original graph-field carrier. The root
calculation uses the published finite Weyl tables and actual Geck conjugation.
No comparison with a different matrix model is assumed.

This is a counterexample to the proposed local interface, not to
Aschbacher--Smith E.1.14(2), printed p.214. That source only cites Asc82a 4.7;
it does not specify this head family or assert this local criterion.
Root conventions: GLS3 §§2.3--2.6 and the existing Head module.
-/

public section

open Subgroup
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.Parabolics.CentralRootSquare
open Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Theory.AlgebraicGroup.StandardRootSystem
open CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction

noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction.HeadCounterexample

private def numbered : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbered_generator (i : Fin 4) :
    numbered (rootWeylGenerator i) = DiagramFixed.reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm (rootReflection i (rootEnumeration r)) = reflectionTable i r
  rw [rootReflection, ← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma numbered_representative (w : DihedralGroup 6) :
    numbered (rootRepresentative w) = DiagramFixed.representative w := by
  cases w <;>
    simp [rootRepresentative, DiagramFixed.representative, foldedRootReflection,
      map_mul, map_pow, numbered_generator, DiagramFixed.arm]

private lemma representative_root (w : DihedralGroup 6) (r s : Fin 24)
    (h : DiagramFixed.representativeTable w r = s) :
    (rootRepresentative w).val (rootEnumeration r) = rootEnumeration s := by
  have he := Equiv.congr_fun (numbered_representative w) r
  change rootEnumeration.symm ((rootRepresentative w).val (rootEnumeration r)) = _ at he
  rw [DiagramFixed.representative_apply, h] at he
  exact rootEnumeration.symm.injective (he.trans (rootEnumeration.symm_apply_apply s).symm)

private lemma highestReflection_fixes_arms (i : Fin 3) :
    (rootRepresentative (.sr 3)).val (rootIndex (shortPosition 0 i)) =
      rootIndex (shortPosition 0 i) := by
  rw [← rootEnumeration_positiveIndex]
  exact representative_root (.sr 3) _ _ (by fin_cases i <;> decide +kernel)

private lemma highestTransport_central :
    (rootRepresentative (.r 5)).val (rootIndex 3) = rootIndex 11 := by
  rw [← rootEnumeration_positiveIndex, ← rootEnumeration_positiveIndex]
  exact representative_root (.r 5) _ _ (by decide +kernel)

private lemma conjugate_curve (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 12)
    (h : (rootRepresentative w).val (rootIndex i) = rootIndex j) (t : ExtensionField P) :
    splitRepresentative P hp w * curve P i t * (splitRepresentative P hp w)⁻¹ =
      curve P j t := by
  have hc := (InputRealization.inputs P hp).conjugate_root (rootRepresentative w)
    (rootIndex i) t
  change (InputRealization.inputs P hp).lift (rootRepresentative w) * _ *
    ((InputRealization.inputs P hp).lift (rootRepresentative w))⁻¹ = _ at hc
  simpa only [FixedDescent.lift_rootRepresentative, SplitNormalForm.rootCurve_positive, h]
    using hc

private lemma headHom_formula (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) (u v : fixedField P) :
    headHom P hp (Multiplicative.ofAdd (t, ![u,v])) =
      short P hp 0 t * long P hp 1 u * long P hp 2 v := by
  change (coordinates P hp (headParameters P (t, ![u,v]))).val = _
  rw [coordinates_val, rootElement_factorization]
  simp [headParameters, extendOrbit]

private def shortHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (ExtensionField P) →* Carrier P :=
  (headHom P hp).comp
    { toFun := fun t => Multiplicative.ofAdd (t.toAdd, 0)
      map_one' := rfl
      map_mul' := fun a b => by
        change Multiplicative.ofAdd (a.toAdd + b.toAdd, 0) =
          Multiplicative.ofAdd ((a.toAdd, (0 : Fin 2 → fixedField P)) + (b.toAdd, 0))
        simp only [Prod.mk_add_mk, add_zero] }

private lemma shortHom_apply (P : Parameters) (hp : P.prime = 2)
    (t : Multiplicative (ExtensionField P)) : shortHom P hp t = short P hp 0 t.toAdd := by
  have h := headHom_formula P hp t.toAdd 0 0
  have hz : (![0, 0] : Fin 2 → fixedField P) = 0 := by ext i; fin_cases i <;> rfl
  simpa only [shortHom, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    long_zero, mul_one, hz] using h

private def witness (P : Parameters) (hp : P.prime = 2) : Carrier P :=
  weylRepresentative P hp (.sr 3)

private lemma witness_centralizes_short (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    witness P hp * short P hp 0 t * (witness P hp)⁻¹ = short P hp 0 t := by
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul, map_inv, witness, FixedDescent.carrierToSplit_representative,
    short, FixedDescent.carrierToSplit_toCarrier, shortElementary_val]
  have h (i : Fin 3) (s : ExtensionField P) :=
    conjugate_curve P hp (.sr 3) (shortPosition 0 i) (shortPosition 0 i)
      (highestReflection_fixes_arms i) s
  change (MulAut.conj (splitRepresentative P hp (.sr 3))) (shortSplit P 0 t) = _
  simp only [shortSplit, map_mul, MulAut.conj_apply, h]

private lemma witness_not_parabolic (f : ℕ) (hf : 0 < f) :
    witness (binaryParameters f hf) rfl ∉ parabolic (binaryParameters f hf) .central := by
  have hc : witness (binaryParameters f hf) rfl ∈ cell (binaryParameters f hf) rfl (.sr 3) :=
    (mem_cell_iff _ _ _ _).mpr ⟨1, (borel _).one_mem, 1, (borel _).one_mem, by simp [witness]⟩
  rw [FixedDescent.mem_parabolic_iff_of_mem_cell f hf .central hc,
    FoldedCellGeometry.rootRepresentative_mem_parabolicWeyl_iff]
  decide

private lemma highest_conjugate (P : Parameters) (hp : P.prime = 2) :
    (MulAut.conj (weylRepresentative P hp (.r 5)))
      (ConcreteBruhat.rootElement P hp true .central 1) = long P hp 2 1 := by
  have hr : elementaryInclusion P (ConcreteBruhat.rootElementary P hp true .central 1) =
      curve P 3 1 := (curve_simple P 1 1).symm
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [MulAut.conj_apply, map_mul, map_inv, FixedDescent.carrierToSplit_representative,
    ConcreteBruhat.rootElement, FixedDescent.carrierToSplit_toCarrier,
    long, longElementary_val, hr]
  exact conjugate_curve P hp (.r 5) 3 11 highestTransport_central 1

private lemma witness_conjugate (P : Parameters) (hp : P.prime = 2) :
    witness P hp = (MulAut.conj (weylRepresentative P hp (.r 5)))
      (simpleRepresentative P hp .central) := by
  rw [← weylRepresentative_simple P hp .central]
  change weylRepresentativeHom P hp (.sr 3) =
    weylRepresentativeHom P hp (.r 5) * weylRepresentativeHom P hp (.sr 1) *
      (weylRepresentativeHom P hp (.r 5))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

private lemma witness_root_word (P : Parameters) (hp : P.prime = 2) :
    witness P hp = long P hp 2 1 *
      (witness P hp * long P hp 2 1 * (witness P hp)⁻¹) * long P hp 2 1 := by
  have hsinv : (simpleRepresentative P hp .central)⁻¹ =
      simpleRepresentative P hp .central :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using simpleRepresentative_sq P hp .central)
  have hword : simpleRepresentative P hp .central =
      ConcreteBruhat.rootElement P hp true .central 1 *
      (simpleRepresentative P hp .central * ConcreteBruhat.rootElement P hp true .central 1 *
        (simpleRepresentative P hp .central)⁻¹) *
      ConcreteBruhat.rootElement P hp true .central 1 := by
    rw [hsinv, simpleRepresentative_positive]
    exact simpleRepresentative_eq_root_word P hp .central
  have he := congrArg (MulAut.conj (weylRepresentative P hp (.r 5))) hword
  simpa only [map_mul, map_inv, ← witness_conjugate, highest_conjugate] using he

private lemma highest_mem_head (P : Parameters) (hp : P.prime = 2) :
    long P hp 2 1 ∈ headSubgroup P hp := by
  refine ⟨Multiplicative.ofAdd (0, ![0,1]), ?_⟩
  simpa only [short_zero, long_zero, one_mul] using headHom_formula P hp 0 0 1

private lemma witness_not_normalizer_head (f : ℕ) (hf : 0 < f) :
    witness (binaryParameters f hf) rfl ∉
      normalizer (headSubgroup (binaryParameters f hf) rfl : Set _) := by
  intro hw
  let P := binaryParameters f hf
  have hp : P.prime = 2 := rfl
  have hz := highest_mem_head P hp
  have hconj := (mem_normalizer_iff.mp hw (long P hp 2 1)).mp hz
  have hg : witness P hp ∈ headSubgroup P hp := by
    rw [witness_root_word P hp]
    exact (headSubgroup P hp).mul_mem ((headSubgroup P hp).mul_mem hz hconj) hz
  exact witness_not_parabolic f hf
    (((headSubgroup_le_unipotent P hp).trans
      ((unipotent_le_borel P).trans (borel_le_parabolic P .central))) hg)

private def shortHead (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (shortHom P hp).range

private lemma shortHead_le_head (P : Parameters) (hp : P.prime = 2) :
    shortHead P hp ≤ headSubgroup P hp := by
  rintro _ ⟨t, rfl⟩
  exact ⟨Multiplicative.ofAdd (t.toAdd, 0), rfl⟩

private lemma shortHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (shortHom P hp) := by
  intro s t h
  have he := headHom_injective P hp h
  exact congrArg (fun x : Multiplicative (TwoRank.TailParameters P) =>
    Multiplicative.ofAdd x.toAdd.1) he

private lemma card_shortHead (P : Parameters) (hp : P.prime = 2) :
    Nat.card (shortHead P hp) = P.q ^ 3 := by
  rw [shortHead, ← Nat.card_congr (MonoidHom.ofInjective (shortHom_injective P hp)).toEquiv]
  exact card_extensionField P

private lemma head_le_normalizer_shortHead (P : Parameters) (hp : P.prime = 2) :
    headSubgroup P hp ≤ normalizer (shortHead P hp : Set _) := by
  have hc : headSubgroup P hp ≤ centralizer (shortHead P hp : Set _) := by
    let _ := headSubgroup_elementary P hp
    let _ : CommGroup (headSubgroup P hp) := IsMulCommutative.instCommGroup
    intro a ha
    apply mem_centralizer_iff.mpr
    intro q hq
    exact congrArg Subtype.val
      (mul_comm (⟨q, shortHead_le_head P hp hq⟩ : headSubgroup P hp) ⟨a, ha⟩)
  exact hc.trans (centralizer_le_normalizer _)

private lemma witness_mem_normalizer_shortHead (P : Parameters) (hp : P.prime = 2) :
    witness P hp ∈ normalizer (shortHead P hp : Set _) := by
  apply centralizer_le_normalizer
  apply mem_centralizer_iff.mpr
  rintro _ ⟨t, rfl⟩
  rw [shortHom_apply]
  exact ((mul_inv_eq_iff_eq_mul).mp (witness_centralizes_short P hp t.toAdd)).symm

private lemma carrier_twoCore_eq_bot (f : ℕ) (hf : 0 < f) :
    pCore 2 (BinaryCarrier f hf) = ⊥ := by
  by_contra h
  obtain ⟨g, a, ha⟩ := Triality.Standard.TwoLocalCover.normalizer_cover f hf
    (pCore 2 (BinaryCarrier f hf)) h pCore_isPGroup
  rw [normalizer_eq_top, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at ha
  exact parabolic_ne_top_binary (binaryParameters f hf) rfl a (top_unique ha)

private lemma tau_le_normalizer_shortHead (f : ℕ) (hf : 0 < f) :
    CFSG.Quasithin.ChapterE.tau (unipotent (binaryParameters f hf))
      (headSubgroup (binaryParameters f hf) rfl) ≤
        normalizer (shortHead (binaryParameters f hf) rfl : Set _) := by
  apply le_trans _ (centralizer_le_normalizer _)
  intro t ht
  obtain ⟨_, hc⟩ := mem_centralizerModulo_iff.mp ht
  apply mem_centralizer_iff.mpr
  intro q hq
  have h := hc q (shortHead_le_head _ rfl hq)
  rw [carrier_twoCore_eq_bot f hf, mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h
  exact h

/-- The requested local criterion fails for the literal head at every positive
binary exponent. This does not refute the source E.1.14(2). -/
theorem head_normalizer_criterion_counterexample (f : ℕ) (hf : 0 < f) :
    ∃ A Q : Subgroup (BinaryCarrier f hf),
      A ∈ headFamily f hf ∧ A ≤ unipotent (binaryParameters f hf) ∧
      Q ≤ unipotent (binaryParameters f hf) ∧ IsPGroup 2 Q ∧
      A ≤ normalizer (Q : Set (BinaryCarrier f hf)) ∧
      CFSG.Quasithin.ChapterE.tau (unipotent (binaryParameters f hf)) A ≤
        normalizer (Q : Set (BinaryCarrier f hf)) ∧
      2 ^ (2 * f) < Nat.card (Q ⊓ A : Subgroup (BinaryCarrier f hf)) ∧ ¬ A ≤ Q ∧
      ¬ (normalizer (Q : Set (BinaryCarrier f hf)) ≤ normalizer (A : Set (BinaryCarrier f hf)) ∨
        normalizer (Q : Set (BinaryCarrier f hf)) ≤ parabolic (binaryParameters f hf) .central) := by
  let P := binaryParameters f hf
  have hp : P.prime = 2 := rfl
  let A := headSubgroup P hp
  let Q := shortHead P hp
  have hQA : Q ≤ A := shortHead_le_head P hp
  have hAU : A ≤ unipotent P := headSubgroup_le_unipotent P hp
  have hQU : Q ≤ unipotent P := hQA.trans hAU
  refine ⟨A, Q, headSubgroup_mem, hAU, hQU,
    (unipotent_isPGroup_binary P hp).to_le hQU,
    head_le_normalizer_shortHead P hp, tau_le_normalizer_shortHead f hf, ?_, ?_, ?_⟩
  · rw [inf_eq_left.mpr hQA, card_shortHead, binaryParameters_q, ← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  · intro hAQ
    have hc := Subgroup.card_le_of_le hAQ
    rw [card_headSubgroup, card_shortHead] at hc
    have hlt : P.q ^ 3 < P.q ^ 5 :=
      Nat.pow_lt_pow_right (by have := P.q_ge_two; omega) (by decide)
    exact (not_lt_of_ge hc) hlt
  · intro h
    have hw := witness_mem_normalizer_shortHead P hp
    rcases h with h | h
    · exact witness_not_normalizer_head f hf (h hw)
    · exact witness_not_parabolic f hf (h hw)

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction.HeadCounterexample
