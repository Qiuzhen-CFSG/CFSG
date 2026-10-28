module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent.RootCells
public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent.AlgebraicCells.Collection
public import Theory.AlgebraicGroup.Unipotent.SolvableTorusDecomposition
public import Theory.AlgebraicGroup.Bor1.GeometricCertificates
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.CellSeparation.SolvableTori

/-!
# Algebraic inputs to root-cell geometry

Opposite Borels supply the disjointness clauses, and the solvable torus
decomposition supplies the Borel factors. Trivial torus fixed points in the
positive radical then give `B ∩ N(T) = T`: the unipotent factor of a normalizer element
centralizes the torus, since its commutators lie in both the radical and
the torus. Solvable conjugacy of maximal tori separates the double cosets.
Conjugation by the actual normalizer element reverses the orientation of
the checked separation theorem from `n⁻¹*m` to `m*n⁻¹`.

The final construction below still takes trivial radical fixed points and actual
arbitrary-order root products with their conjugation destinations explicitly.
It is a conditional construction, not yet the source theorem for every
connected simple algebraic group. Its source assembly must discharge those
premises. Neither a BN-pair nor global Bruhat coverage is assumed.

Source: GLS3 1.11.3--1.11.5 and 1.12.7,
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg 6.2--6.3,
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells

universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]
  {B C U V T : ClosedSubgroup K}

omit [IsAlgClosed k] in
/-- Relative normality of a radical gives normalization by its overgroup. -/
theorem radical_normalizer (hU : IsUnipotentRadicalOf B U) :
    B.toSubgroup ≤ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point K)) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ U ↔ b * x * b⁻¹ ∈ U
  constructor
  · exact hU.2.2.1 b hb x
  · intro hx
    have h := hU.2.2.1 b⁻¹ (B.inv_mem hb) (b * x * b⁻¹) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one] using h

/-- The specified Borel and its actual radical have the required `U*T` order. -/
theorem borel_factors (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hT : IsMaximalTorus T) (hTB : T ≤ B) :
    ∀ b ∈ B.toSubgroup, ∃ u ∈ U.toSubgroup, ∃ t ∈ T.toSubgroup, b = u * t := by
  intro b hb
  obtain ⟨t, u, ht, hu, heq⟩ :=
    (maximalTorus_unipotentRadical_decomposition_of_connected_solvable
      hB.connected hB.solvable hU hT hTB).1 b hb
  refine ⟨t * u * t⁻¹, hU.2.2.1 t (hTB ht) u hu, t, ht, ?_⟩
  rw [heq]
  group

/-- The opposite radical is disjoint from the entire first Borel. -/
theorem negative_disjoint_borel (hV : IsUnipotentRadicalOf C V)
    (hT : IsSubtorus T) (hBC : B.inter C = T) :
    Disjoint V.toSubgroup B.toSubgroup := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hxT : x ∈ T.toSubgroup := by
    change x ∈ T
    rw [← hBC]
    exact ⟨hx.2, hV.1 hx.1⟩
  have h := subtorus_inf_unipotent_eq_bot T V hT hV.2.1
  have hx' : x ∈ T.toSubgroup ⊓ V.toSubgroup := ⟨hxT, hx.1⟩
  rwa [h] at hx'

/-- Trivial radical fixed points and solvable decomposition identify the literal
Borel-normalizer intersection. No Weyl quotient is substituted for it. -/
theorem borel_inf_normalizer_of_fixed_radical
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hfixed : (U.pointwiseCentralizer T).toSubgroup = ⊥) :
    B.toSubgroup ⊓ T.normalizer.toSubgroup = T.toSubgroup := by
  apply le_antisymm _ (le_inf hTB T.toSubgroup.le_normalizer)
  intro n hn
  obtain ⟨t, x, ht, hx, heq⟩ :=
    (maximalTorus_unipotentRadical_decomposition_of_connected_solvable
      hB.connected hB.solvable hU hT hTB).1 n hn.1
  have hxN : x ∈ T.normalizer.toSubgroup := by
    have h := T.normalizer.mul_mem
      (T.normalizer.inv_mem (T.toSubgroup.le_normalizer ht)) hn.2
    rw [heq] at h
    simpa only [inv_mul_cancel_left] using h
  have hxC : x ∈ T.centralizer.toSubgroup := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hcomT : z⁻¹ * x * z * x⁻¹ ∈ T.toSubgroup := by
      have h := (Subgroup.mem_normalizer_iff.mp hxN z).mp hz
      simpa only [mul_assoc] using T.mul_mem (T.inv_mem hz) h
    have hcomU : z⁻¹ * x * z * x⁻¹ ∈ U.toSubgroup := by
      have h := hU.2.2.1 z⁻¹ (hTB (T.inv_mem hz)) x hx
      simpa only [inv_inv] using U.mul_mem h (U.inv_mem hx)
    have hone : z⁻¹ * x * z * x⁻¹ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← subtorus_inf_unipotent_eq_bot T U hT.1 hU.2.1]
      exact ⟨hcomT, hcomU⟩
    have h := congrArg (fun y => z * y * x) hone
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one, one_mul] using h.symm
  have hxone : x = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hfixed]
    exact ⟨hx, hxC⟩
  simpa only [heq, hxone, mul_one] using ht

/-- The checked solvable-torus separation has the orientation required by
`RootCellGeometry.separate` after conjugation by `n`. -/
theorem separate_of_borel_inf_normalizer
    (hB : IsBorelSubgroup B) (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hBN : B.toSubgroup ⊓ T.normalizer.toSubgroup = T.toSubgroup)
    (n : Variety.Point K) (hn : n ∈ T.normalizer.toSubgroup)
    (m : Variety.Point K) (hm : m ∈ T.normalizer.toSubgroup)
    (b : Variety.Point K) (hb : b ∈ B.toSubgroup)
    (c : Variety.Point K) (hc : c ∈ B.toSubgroup)
    (heq : m = b * n * c) : m * n⁻¹ ∈ T.toSubgroup := by
  have h := Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Bruhat.Splitting.CellSeparation.coset_separation
      B T hB.solvable hT hTB hBN ⟨n, hn⟩ ⟨m, hm⟩ b c 1 1 hb hc
      B.one_mem B.one_mem (by simpa only [one_mul, mul_one] using heq.symm)
  have hconj := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * m)).mp h
  simpa only [mul_inv_cancel_left] using hconj

/-- Construct every root-cell field from actual opposite Borel radicals,
trivial radical fixed points, and arbitrary-order products of subgroups whose
conjugates have a definite sign. The last two inputs remain source obligations. -/
theorem nonempty_rootCellGeometry_of_ordered_products
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U)
    (hV : IsUnipotentRadicalOf C V) (hT : IsMaximalTorus T)
    (hBC : B.inter C = T)
    (hfixed : (U.pointwiseCentralizer T).toSubgroup = ⊥)
    {ι : Type v} (A : ι → Subgroup (Variety.Point K)) (P : Set ι)
    (roots : List ι) (hnd : roots.Nodup) (hroots : ∀ i, i ∈ roots ↔ i ∈ P)
    (hA : ∀ i ∈ P, A i ≤ U.toSubgroup)
    (hproduct : ∀ order : List ι, order.Nodup →
      (∀ i, i ∈ order ↔ i ∈ P) → ∀ q ∈ U.toSubgroup,
        ∃ xs : List (Variety.Point K),
          List.Forall₂ (fun i x => x ∈ A i) order xs ∧ xs.prod = q)
    (htransport : ∀ n ∈ T.normalizer.toSubgroup, ∀ i ∈ P,
      A i ≤ U.toSubgroup.comap (MulAut.conj n).toMonoidHom ∨
      A i ≤ V.toSubgroup.comap (MulAut.conj n).toMonoidHom) :
    Nonempty (RootCellGeometry B.toSubgroup U.toSubgroup T.toSubgroup
      T.normalizer.toSubgroup V.toSubgroup) := by
  have hTB : T ≤ B := by
    intro x hx
    rw [← hBC] at hx
    exact hx.1
  have hTC : T ≤ C := by
    intro x hx
    rw [← hBC] at hx
    exact hx.2
  refine ⟨{
    positive_le := hU.1
    torus_le_borel := hTB
    torus_le_normalizer := T.toSubgroup.le_normalizer
    borel_factors := borel_factors hB hU hT hTB
    torus_normalizes_positive := le_trans hTB (radical_normalizer hU)
    torus_normalizes_negative := le_trans hTC (radical_normalizer hV)
    negative_disjoint_borel := negative_disjoint_borel hV hT.1 hBC
    positive_disjoint_torus := ?_
    separate := separate_of_borel_inf_normalizer hB hT hTB
      (borel_inf_normalizer_of_fixed_radical hB hU hT hTB hfixed)
    split := fun n hn q hq => split_of_ordered_products U.toSubgroup V.toSubgroup
      A P roots hnd hroots hA hproduct n (htransport n hn) q hq }⟩
  apply disjoint_iff_inf_le.mpr
  rw [inf_comm, subtorus_inf_unipotent_eq_bot T U hT.1 hU.2.1]

end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells
end
