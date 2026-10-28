module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# Capturing a negative folded root in genuine triality

For every nonidentity relative Weyl word, one complete simple diagram orbit
has positive preimages of its negative roots. A small checked table on the
published twelve Weyl words proves this root-system fact. The actual split
root-conjugation formulas then carry the corresponding central curve or
three-arm product into the conjugate of the positive subgroup.

The faithful map from the original elementary central quotient to the split
matrices preserves this containment. Both signs, all root-field parameters,
and the three Frobenius-related arm coefficients are retained. This supplies
the geometric input to `SolvableSylowControl.le_borel`.

Source: GLS3 2.3.4–8 and §§2.4–2.6,
`refs/KGroup/GLS3/chapter2.tex`; the Borel placement used in the proof of
Aschbacher–Smith 13.6.6, printed p.927 of `refs/quasithin.pdf`.
-/

public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.SolvableSylowControl
open Parabolics ConcreteBruhat PositiveCoordinates
open SplitNormalForm.CellCollection
noncomputable section

private def positiveNumber : Fin 12 → Fin 24 := ![1,21,20,13,5,17,16,9,12,8,4,0]

private def negativeSimpleNumber (i : Fin 4) : Fin 24 := reflectionTable i (simpleIndex i)

private lemma positiveNumber_spec (i : Fin 12) : rootEnumeration (positiveNumber i) = rootIndex i := by
  fin_cases i <;> rfl

private lemma negativeSimpleNumber_spec (i : Fin 4) :
    rootEnumeration (negativeSimpleNumber i) = negativeIndex (typeDSimpleRootIndex 2 i) := by
  rw [negativeSimpleNumber, rootEnumeration_reflectionTable, rootEnumeration_simpleIndex]

private def numbering : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbering_generator (i : Fin 4) :
    numbering (rootWeylGenerator i) = DiagramFixed.reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm ((typeDRootPairing 2).reflectionPerm
    (typeDSimpleRootIndex 2 i) (rootEnumeration r)) = reflectionTable i r
  rw [← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma representative_numbered (w : DihedralGroup 6) (r : Fin 24) :
    (rootRepresentative w).val (rootEnumeration r) =
      rootEnumeration (DiagramFixed.representativeTable w r) := by
  have h : numbering (rootRepresentative w) = DiagramFixed.representative w := by
    cases w <;> simp [rootRepresentative, DiagramFixed.representative, foldedRootReflection,
      map_mul, map_pow, numbering_generator, DiagramFixed.arm]
  have hh := congrFun (congrArg (fun e : Equiv.Perm (Fin 24) => (e : Fin 24 → Fin 24)) h) r
  change rootEnumeration.symm ((rootRepresentative w).val (rootEnumeration r)) = _ at hh
  exact (rootEnumeration.apply_symm_apply _).symm.trans
    (congrArg rootEnumeration (hh.trans (DiagramFixed.representative_apply w r)))

private lemma descent_table (w : DihedralGroup 6) (hw : w ≠ 1) :
    ∃ a : Node, ∀ i : Fin 4, i ∈ a.support → ∃ j : Fin 12,
      DiagramFixed.representativeTable w (positiveNumber j) = negativeSimpleNumber i := by
  have h : ∀ w : DihedralGroup 6, w ≠ 1 →
      (∀ i : Fin 4, i ≠ 1 → ∃ j : Fin 12,
        DiagramFixed.representativeTable w (positiveNumber j) = negativeSimpleNumber i) ∨
      (∃ j : Fin 12, DiagramFixed.representativeTable w (positiveNumber j) =
        negativeSimpleNumber 1) := by decide +kernel
  rcases h w hw with h | h
  · exact ⟨.arms, h⟩
  · refine ⟨.central, ?_⟩
    intro i hi
    have hi : i = 1 := hi
    subst i
    exact h

private lemma exists_negative_simple_preimages (w : DihedralGroup 6) (hw : w ≠ 1) :
    ∃ a : Node, ∀ i : Fin 4, i ∈ a.support →
      (typeDRootPairing_base 2).IsPos
        (((rootRepresentative w)⁻¹).val (negativeIndex (typeDSimpleRootIndex 2 i))) := by
  obtain ⟨a, ha⟩ := descent_table w hw
  refine ⟨a, ?_⟩
  intro i hi
  obtain ⟨j, hj⟩ := ha i hi
  have he : (rootRepresentative w).val (rootIndex j) =
      negativeIndex (typeDSimpleRootIndex 2 i) := by
    rw [← positiveNumber_spec, representative_numbered, hj, negativeSimpleNumber_spec]
  have he' : ((rootRepresentative w)⁻¹).val
      (negativeIndex (typeDSimpleRootIndex 2 i)) = rootIndex j := by
    rw [← he]
    exact Equiv.symm_apply_apply _ _
  rw [he']
  exact rootIndex_positive j

private lemma rootCurve_negative_simple (P : Parameters) (i : Fin 4)
    (t : ExtensionField P) :
    SplitNormalForm.rootCurve P (negativeIndex (typeDSimpleRootIndex 2 i)) t =
      negativeRoot P i t := by
  apply Subtype.ext
  exact RootPairing.IntegralGeckConstruction.rootCurveUnit_neg_simple
    (typeDRootPairing_baseEquiv 2 i) t

private lemma rootCurve_mem_positive (P : Parameters) (hp : P.prime = 2)
    (r : TypeDRootIndex 4) (hr : (typeDRootPairing_base 2).IsPos r)
    (t : ExtensionField P) : SplitNormalForm.rootCurve P r t ∈ positiveSubgroup P := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  have h : r ∈ Set.range rootIndex := by rw [range_rootIndex]; exact hr
  obtain ⟨j, rfl⟩ := h
  exact curve_mem_positiveSubgroup_of_sumExchange _ (sumExchange_binary n hn) j t

private lemma inverse_conjugate_negative_mem (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i : Fin 4)
    (hi : (typeDRootPairing_base 2).IsPos
      (((rootRepresentative w)⁻¹).val (negativeIndex (typeDSimpleRootIndex 2 i))))
    (t : ExtensionField P) :
    (splitRepresentative P hp w)⁻¹ * negativeRoot P i t * splitRepresentative P hp w ∈
      positiveSubgroup P := by
  let D := InputRealization.inputs P hp
  have h := D.conjugate_root ((rootRepresentative w)⁻¹)
    (negativeIndex (typeDSimpleRootIndex 2 i)) t
  change D.lift _ * _ * (D.lift _)⁻¹ = _ at h
  rw [map_inv, FixedDescent.lift_rootRepresentative,
    rootCurve_negative_simple, inv_inv] at h
  rw [h]
  exact rootCurve_mem_positive P hp _ hi t

/-- Every nonidentity relative Weyl word carries some complete positive root
subgroup onto the negative root subgroup at one of the two folded nodes. -/
theorem exists_negative_root_le_conjugate (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (hw : w ≠ 1) :
    ∃ a : Node, ∀ t : RootField P a, rootElement P hp false a t ∈
      (unipotent P).map (MulAut.conj (weylRepresentative P hp w)).toMonoidHom := by
  obtain ⟨a, ha⟩ := exists_negative_simple_preimages w hw
  refine ⟨a, ?_⟩
  intro t
  let n := weylRepresentative P hp w
  have hu : n⁻¹ * rootElement P hp false a t * n ∈ unipotent P := by
    apply (FixedDescent.mem_descend_iff P hp _ _).mpr
    simp only [map_mul, map_inv, n, FixedDescent.carrierToSplit_representative,
      rootElement, FixedDescent.carrierToSplit_toCarrier]
    cases a with
    | central =>
      exact inverse_conjugate_negative_mem P hp w 1 (ha 1 rfl) t.val
    | arms =>
      let L := (positiveSubgroup P).comap
        (MulAut.conj ((splitRepresentative P hp w)⁻¹)).toMonoidHom
      change negativeRoot P 0 t * negativeRoot P 2 (fieldFrobenius P t) *
        negativeRoot P 3 (fieldFrobenius P (fieldFrobenius P t)) ∈ L
      exact L.mul_mem
        (L.mul_mem
          (inverse_conjugate_negative_mem P hp w 0 (ha 0 (by simp [Node.support])) t)
          (inverse_conjugate_negative_mem P hp w 2 (ha 2 (by simp [Node.support])) _))
        (inverse_conjugate_negative_mem P hp w 3 (ha 3 (by simp [Node.support])) _)
  refine ⟨n⁻¹ * rootElement P hp false a t * n, hu, ?_⟩
  change n * (n⁻¹ * rootElement P hp false a t * n) * n⁻¹ = _
  group
end
end Triality.Standard.SolvableSylowControl
