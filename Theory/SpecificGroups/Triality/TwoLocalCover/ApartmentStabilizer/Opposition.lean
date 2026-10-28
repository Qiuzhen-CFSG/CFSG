module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# Concrete triality opposition and the torus bound

The published folded word indexed by `DihedralGroup.r 3` negates all 24 D₄
roots. The checked reflection tables identify its literal root action; the
proved Geck matrix conjugation formula therefore sends the entire positive
subgroup into the negative root closure.

For an element in the Borel and its opposite conjugate, factor the conjugate
as positive times torus. Opposition normalizes the original coroot torus.
Its conjugate of the positive factor is then both negative and in the Borel,
so the proved matrix-height separation makes that factor trivial. Finally the
faithful map from the elementary fixed-point group's own central quotient
transports the bound to the original carrier, also at q = 2.

Source: the opposite-Borel calculation in GLS3 2.3.8(b–d), using 2.3.4–5
and 2.3.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open scoped Pointwise
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.TwoLocalGeometry.ApartmentStabilizer
open Parabolics ConcreteBruhat ConcreteBruhat.SplitNormalForm
noncomputable section
local instance : InvolutiveNeg (TypeDRootIndex 4) := (typeDRootPairing 2).indexNeg

private lemma enumeration_negative (r : Fin 24) :
    rootEnumeration (negativeIndex r) = -rootEnumeration r := by
  apply (typeDRootPairing 2).root_eq_neg_iff.mp
  apply Subtype.ext
  ext k
  simp only [Submodule.coe_neg, Pi.neg_apply, rootCoords_spec]
  rw [rootCoords_negativeIndex]
  simp

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

/-- The published folded opposition word negates every literal D₄ root. -/
theorem opposition_root (r : TypeDRootIndex 4) :
    (rootRepresentative (.r 3)).val r = -r := by
  obtain ⟨r, rfl⟩ := rootEnumeration.surjective r
  rw [representative_numbered, ← enumeration_negative]
  apply congrArg rootEnumeration
  revert r
  decide +kernel

/-- The actual matrix opposition takes the full positive subgroup into the
closure of the canonical negative root curves. -/
theorem opposition_conj_positive (f : ℕ) (hf : 0 < f)
    {u : SplitGroup (binaryParameters f hf)} (hu : u ∈ positiveSubgroup _) :
    splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3) * u *
      (splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3))⁻¹ ∈
        CellSeparation.negativeSubgroup (binaryParameters f hf) := by
  have hu' : u ∈ Set.range (PositiveCoordinates.orderedProduct (binaryParameters f hf)) := by
    rw [PositiveCoordinates.range_orderedProduct_binary]
    exact hu
  obtain ⟨a, rfl⟩ := hu'
  rw [← FixedDescent.lift_rootRepresentative]
  apply CellSeparation.conjugate_supported_mem_negative
  intro i hi
  rw [opposition_root] at hi
  exact False.elim ((RootPairing.Base.IsPos.neg_iff_not _ _).mp hi
    (PositiveCoordinates.rootIndex_positive i))

/-- An element of the two opposite split Borels lies in the original coroot torus. -/
theorem splitBorel_opposition_intersection (f : ℕ) (hf : 0 < f)
    {x : SplitGroup (binaryParameters f hf)} (hx : x ∈ splitBorel _)
    (hy : (splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3))⁻¹ * x *
      splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3) ∈ splitBorel _) :
    x ∈ splitTorus (binaryParameters f hf) := by
  let P := binaryParameters f hf
  let n := splitRepresentative P (binaryParameters_prime f hf) (.r 3)
  have hn : n ∈ Subgroup.normalizer (splitTorus P) :=
    splitRepresentative_mem_normalizer_splitTorus P (binaryParameters_prime f hf) (.r 3)
  have hy' : n⁻¹ * x * n ∈
      (positiveSubgroup P : Set (SplitGroup P)) * splitTorus P := by
    rw [← splitBorel_eq_mul P (binaryParameters_prime f hf)]
    exact hy
  obtain ⟨u, hu, t, ht, he⟩ := hy'
  have ht' : n * t * n⁻¹ ∈ splitTorus P :=
    (Subgroup.mem_normalizer_iff.mp hn t).mp ht
  have he' : u * t = n⁻¹ * x * n := he
  have heq : (n * u * n⁻¹) * (n * t * n⁻¹) = x := by
    calc
      _ = (MulAut.conj n) (u * t) := (map_mul (MulAut.conj n) u t).symm
      _ = (MulAut.conj n) (n⁻¹ * x * n) := congrArg (MulAut.conj n) he'
      _ = x := by
        change n * (n⁻¹ * x * n) * n⁻¹ = x
        simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]
  have huB : n * u * n⁻¹ ∈ splitBorel P := by
    have hh := (splitBorel P).mul_mem hx
      ((splitBorel P).inv_mem (splitTorus_le_splitBorel P ht'))
    rw [← heq, mul_inv_cancel_right] at hh
    exact hh
  have hu1 : n * u * n⁻¹ = 1 :=
    Subgroup.disjoint_def.mp
      (CellSeparation.borel_inf_negative f hf (InputRealization.inputs P (binaryParameters_prime f hf)))
      huB (opposition_conj_positive f hf hu)
  rw [← heq, hu1, one_mul]
  exact ht'

/-- Faithful descent from the original elementary central quotient preserves
the opposite-Borel torus bound. -/
theorem borel_opposition_intersection (f : ℕ) (hf : 0 < f)
    {x : Carrier (binaryParameters f hf)} (hx : x ∈ borel _)
    (hy : (weylRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3))⁻¹ * x *
      weylRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3) ∈ borel _) :
    x ∈ torus (binaryParameters f hf) := by
  apply (FixedDescent.mem_descend_iff _ (binaryParameters_prime f hf) _ x).mpr
  apply splitBorel_opposition_intersection f hf
    ((FixedDescent.mem_descend_iff _ (binaryParameters_prime f hf) _ x).mp hx)
  have h := (FixedDescent.mem_descend_iff (binaryParameters f hf)
    (binaryParameters_prime f hf) (splitBorel _) _).mp hy
  simpa only [map_mul, map_inv, FixedDescent.carrierToSplit_representative] using h

end
end Triality.Standard.TwoLocalGeometry.ApartmentStabilizer
