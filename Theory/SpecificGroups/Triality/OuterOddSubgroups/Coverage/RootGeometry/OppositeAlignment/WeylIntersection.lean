module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.Basic


/-!
# A disjoint Weyl conjugate is opposite

For each of the eleven nonlong relative Weyl words, the literal D₄ reflection
tables exhibit a simple diagram orbit whose roots remain positive. Conjugating
the corresponding folded root element at parameter one therefore gives a
nonidentity element in both positive subgroups. Injectivity of the actual root
parameter map survives the elementary central quotient, including at q = 2.
Thus disjointness forces the published longest word, indexed by `.r 3`.

This is the Weyl-intersection step used by the opposite-unipotent alignment
in the parent module. It requires neither simplicity nor root recognition.
Source: Steinberg, Theorem 30(1) and the proof of Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 2.3.5 and 2.3.8(c),
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.OuterOdd.Coverage.RootGeometry.OppositeAlignment
open Parabolics ConcreteBruhat ConcreteBruhat.SplitNormalForm PositiveCoordinates
noncomputable section

private def positiveNumber : Fin 12 → Fin 24 := ![1,21,20,13,5,17,16,9,12,8,4,0]
private def simpleNumber : Fin 4 → Fin 24 := ![1,13,21,20]
private lemma positiveNumber_spec (i : Fin 12) :
    rootEnumeration (positiveNumber i) = rootIndex i := by
  fin_cases i <;> rfl
private lemma simpleNumber_spec (i : Fin 4) :
    rootEnumeration (simpleNumber i) = typeDSimpleRootIndex 2 i := by
  fin_cases i <;> rfl
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

private theorem exists_positive_node (w : DihedralGroup 6) (hw : w ≠ .r 3) :
    ∃ a : Node, ∀ i ∈ a.support, ∃ j : Fin 12,
      (rootRepresentative w).val (typeDSimpleRootIndex 2 i) = rootIndex j := by
  have h : ∀ w : DihedralGroup 6, w ≠ .r 3 →
      (∀ i ∈ Node.arms.support, ∃ j : Fin 12,
        DiagramFixed.representativeTable w (simpleNumber i) = positiveNumber j) ∨
      (∀ i ∈ Node.central.support, ∃ j : Fin 12,
        DiagramFixed.representativeTable w (simpleNumber i) = positiveNumber j) := by
    simp only [Node.support, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    decide +kernel
  have hex : ∃ a : Node, ∀ i ∈ a.support, ∃ j : Fin 12,
      DiagramFixed.representativeTable w (simpleNumber i) = positiveNumber j := by
    rcases h w hw with h | h
    · exact ⟨.arms, h⟩
    · exact ⟨.central, h⟩
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, fun i hi => ?_⟩
  obtain ⟨j, hj⟩ := ha i hi
  exact ⟨j, by rw [← simpleNumber_spec, representative_numbered, hj, positiveNumber_spec]⟩

private theorem conjugate_simple_mem_positive (f : ℕ) (hf : 0 < f)
    (w : DihedralGroup 6) (i : Fin 4)
    (hi : ∃ j : Fin 12, (rootRepresentative w).val (typeDSimpleRootIndex 2 i) = rootIndex j)
    (t : ExtensionField (binaryParameters f hf)) :
    splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) w *
      positiveRoot _ i t *
      (splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) w)⁻¹ ∈
        positiveSubgroup _ := by
  obtain ⟨j, hj⟩ := hi
  have hs : positiveRoot (binaryParameters f hf) i t =
      rootCurve _ (typeDSimpleRootIndex 2 i) t := by
    rw [← rootIndex_simple, rootCurve_positive, curve_simple]
  rw [← FixedDescent.lift_rootRepresentative, hs, CellCollection.lift_conjugate_root, hj, rootCurve_positive]
  exact curve_mem_positiveSubgroup_of_sumExchange _ (sumExchange_binary f hf) j t

private theorem rootElement_zero (P : Parameters) (hp : P.prime = 2) (a : Node) :
    rootElement P hp true a 0 = 1 := by
  have he : rootElementary P hp true a 0 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    cases a with
    | arms =>
      change positiveRoot P 0 0 * positiveRoot P 2 (fieldFrobenius P 0) *
        positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P 0)) = 1
      simp only [map_zero, positiveRoot_zero, one_mul]
    | central => exact positiveRoot_zero P 1
  exact (congrArg (toCarrier P) he).trans (map_one _)

private theorem conjugate_root_mem_unipotent (f : ℕ) (hf : 0 < f)
    (w : DihedralGroup 6) (a : Node)
    (ha : ∀ i ∈ a.support, ∃ j : Fin 12,
      (rootRepresentative w).val (typeDSimpleRootIndex 2 i) = rootIndex j)
    (t : RootField (binaryParameters f hf) a) :
    weylRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) w *
      rootElement _ (binaryParameters_prime f hf) true a t *
      (weylRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) w)⁻¹ ∈ unipotent _ := by
  apply (FixedDescent.mem_descend_iff (binaryParameters f hf) (binaryParameters_prime f hf)
    (positiveSubgroup (binaryParameters f hf)) _).mpr
  simp only [map_mul, map_inv, FixedDescent.carrierToSplit_representative,
    rootElement, FixedDescent.carrierToSplit_toCarrier]
  let P := binaryParameters f hf
  let n := splitRepresentative P (binaryParameters_prime f hf) w
  have hc (i : Fin 4) (hi : i ∈ a.support) (s : ExtensionField P) :
      n * positiveRoot P i s * n⁻¹ ∈ positiveSubgroup P :=
    conjugate_simple_mem_positive f hf w i (ha i hi) s
  cases a with
  | arms =>
    change n * (positiveRoot P 0 t * positiveRoot P 2 (fieldFrobenius P t) *
      positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t))) * n⁻¹ ∈ positiveSubgroup P
    change (MulAut.conj n) (_ * _ * _) ∈ _
    simp only [map_mul]
    exact (positiveSubgroup P).mul_mem ((positiveSubgroup P).mul_mem
      (hc 0 (by simp [Node.support]) _) (hc 2 (by simp [Node.support]) _))
        (hc 3 (by simp [Node.support]) _)
  | central =>
    exact hc 1 (by simp [Node.support]) t.val

/-- Only the literal longest relative word gives a disjoint positive conjugate. -/
theorem weyl_eq_opposition_of_disjoint (f : ℕ) (hf : 0 < f) (w : DihedralGroup 6)
    (hd : Disjoint (unipotent (binaryParameters f hf))
      ((unipotent (binaryParameters f hf)).map
        (MulAut.conj (weylRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) w)).toMonoidHom)) :
    w = .r 3 := by
  by_contra hw
  obtain ⟨a, ha⟩ := exists_positive_node w hw
  let P := binaryParameters f hf
  have he : weylRepresentative P (binaryParameters_prime f hf) w *
      rootElement P (binaryParameters_prime f hf) true a 1 *
      (weylRepresentative P (binaryParameters_prime f hf) w)⁻¹ = 1 :=
    Subgroup.disjoint_def.mp hd (conjugate_root_mem_unipotent f hf w a ha 1)
      ⟨rootElement P (binaryParameters_prime f hf) true a 1,
        positive_mem_unipotent P (binaryParameters_prime f hf) a 1, rfl⟩
  have hz : rootElement P (binaryParameters_prime f hf) true a 1 =
      rootElement P (binaryParameters_prime f hf) true a 0 := by
    rw [rootElement_zero]
    exact (MulAut.conj (weylRepresentative P (binaryParameters_prime f hf) w)).injective
      (he.trans (map_one _).symm)
  exact one_ne_zero (rootElement_injective P (binaryParameters_prime f hf) true a hz)

end
end Triality.Standard.OuterOdd.Coverage.RootGeometry.OppositeAlignment
