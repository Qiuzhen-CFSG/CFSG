module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells.OppositeCollection
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.NegativeExchange

/-!
# Opposite-unipotent Bruhat cells in the actual algebraic F4 carrier

Every carrier point over an algebraically closed field of characteristic two
has the form `positive roots * direct coroots * negative roots * simple word`.
Both root orderings may be prescribed. The Weyl factor is the literal list
product of parameter-one simple normalizer elements.

Starting with the generic carrier `U N U` cover, root transport partitions the
right positive subgroup according to the signs of the transported roots.
The positive part is absorbed on the left. Negative-root collection and the
explicit normalizer-word decomposition finish the opposite-root chart. No
finite-field membership, density, root uniqueness, or rational parameter
recovery is used.

Source: Steinberg, *Lectures on Chevalley Groups*, Theorem 4′(a) and the third
corollary to Theorem 7, `refs/KGroup/GLS3/Chapter2St1.tex`, pp. 36–37, 67.
-/

public section
noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open F4Chevalley F4Chevalley.DenseParameters F4Chevalley.DenseParameters.CarrierBruhat
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
local instance restrictedCellsRootNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
open RestrictedCells

private theorem exists_opposite_factors (x : Variety.Point (Carrier (k := F))) :
    ∃ u ∈ positiveUnipotent (k := F), ∃ v ∈ negativeUnipotent (k := F),
      ∃ n ∈ normalizerWords (k := F), x = u * v * n := by
  obtain ⟨u, hu, n, hn, v, hv, hx⟩ :=
    exists_unrestricted_factors_of_negativeSimpleExchange
      (negativeSimpleExchange_of_partition positiveRootPartition
        (fun _ hn => normalizerWords_rootTransport hn)) x
  obtain ⟨T⟩ := normalizerWords_rootTransport hn
  let f := (MulAut.conj n).toMonoidHom
  have hroot (r : CarrierBruhat.PositiveRoot) :
      (∀ a : F, rootElement r.val a ∈ (positiveUnipotent (k := F)).comap f) ∨
      (∀ a : F, rootElement r.val a ∈ (negativeUnipotent (k := F)).comap f) := by
    by_cases hp : typeF4RootPairing_base.IsPos (T.perm r.val)
    · left
      intro a
      change n * rootElement r.val a * n⁻¹ ∈ positiveUnipotent
      rw [T.conj_root]
      exact rootElement_mem_positiveUnipotent _ hp _
    · right
      intro a
      change n * rootElement r.val a * n⁻¹ ∈ negativeUnipotent
      rw [T.conj_root]
      exact rootElement_mem_negativeUnipotent _ hp _
  obtain ⟨a, ha, b, hb, hab⟩ := positiveRootPartition
    ((positiveUnipotent (k := F)).comap f) ((negativeUnipotent (k := F)).comap f)
    hroot v hv
  refine ⟨u * f a, (positiveUnipotent (k := F)).mul_mem hu ha,
    f b, hb, n, hn, ?_⟩
  rw [hx, hab]
  change u * n * (a * b) = (u * (n * a * n⁻¹)) * (n * b * n⁻¹) * n
  group

/-- Unconditional coverage of the actual algebraic carrier by literal
opposite-root cells, for any prescribed positive root orderings. -/
theorem exists_cell_of_positiveOrderings (o o' : PositiveOrdering)
    (x : Variety.Point (F4Chevalley.Carrier (k := F))) :
    ∃ (a b : Fin 24 → F) (t : Fin 4 → Fˣ) (l : List (Fin 4)),
      x = cell (fun i => (o i).val) (fun i => -(o' i).val) a t b l := by
  obtain ⟨u, hu, v, hv, n, hn, hx⟩ := exists_opposite_factors x
  obtain ⟨t, l, hn'⟩ := normalizerWords_eq_corootProduct_mul_weylWord hn
  obtain ⟨a, ha⟩ := orderedPositiveCoverage o u hu
  obtain ⟨b, hb⟩ := orderedNegativeCoverage o'
    ((corootProduct t)⁻¹ * v * corootProduct t) (corootProduct_inv_conj_negative t hv)
  refine ⟨a, b, t, l, ?_⟩
  change x = rootProduct (fun i => (o i).val) a * corootProduct t *
    rootProduct (fun i => -(o' i).val) b * weylWord l
  have ha' : u = rootProduct (fun i => (o i).val) a := ha
  rw [← ha', ← hb, hx, hn']
  group

/-- Two genuine positive orderings give opposite-root cells covering every
point of the closed root-generated F4 carrier. The signs use the actual root
negation, the coroots are `n(t)n(1)⁻¹`, and the Weyl factor is a literal list. -/
theorem exists_positiveOrderings_cell_cover :
    ∃ o o' : PositiveOrdering,
      ∀ x : Variety.Point (F4Chevalley.Carrier (k := F)),
        ∃ (a b : Fin 24 → F) (t : Fin 4 → Fˣ) (l : List (Fin 4)),
          x = cell (fun i => (o i).val) (fun i => -(o' i).val) a t b l :=
  ⟨positiveOrdering, positiveOrdering, exists_cell_of_positiveOrderings _ _⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
