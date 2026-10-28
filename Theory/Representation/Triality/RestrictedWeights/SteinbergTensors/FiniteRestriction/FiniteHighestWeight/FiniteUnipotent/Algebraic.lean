module

public import Theory.AlgebraicGroup.Borel.HighestWeight

/-!
# Algebraic unipotent fixed lines and highest-vector orbits

The opposite-Borel big cell proves two algebraic facts needed for finite
restriction. Positive-unipotent fixed vectors form the highest line, and the
opposite-unipotent orbit of a highest vector spans the representation.

For the first assertion, an opposite highest-weight functional separates all
positive-unipotent fixed vectors: a vector in its kernel has a matrix
coefficient vanishing on the reverse big cell, hence everywhere. For the
second assertion, any functional annihilating the opposite-unipotent orbit
likewise vanishes on that dense cell.

These assertions concern the full algebraic unipotent groups. They make no
claim about finite fixed points. Source: GLS3, Theorem 1.14.6(c), and the
big-cell argument used before the restriction theorem in Section 2.8.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise

universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [IsAlgClosed k] in
private lemma reverseCell_dense (H : OppositeBorelBigCell T D P) :
    Dense ((H.data.Bopp.toSubgroup : Set (Variety.Point K)) *
      (H.data.B.toSubgroup : Set (Variety.Point K))) := by
  let e : Variety.Point K ≃ₜ Variety.Point K :=
    { toFun := fun g => g⁻¹
      invFun := fun g => g⁻¹
      left_inv := inv_inv
      right_inv := inv_inv
      continuous_toFun := (AlgebraicGroup.invMorphism K).continuous
      continuous_invFun := (AlgebraicGroup.invMorphism K).continuous }
  apply (H.product_dense.preimage e.isOpenMap).mono
  intro x hx
  obtain ⟨b, hb, c, hc, hbc⟩ := Set.mem_mul.mp hx
  change b * c = x⁻¹ at hbc
  have h : x = c⁻¹ * b⁻¹ := by rw [← inv_inv x, ← hbc, mul_inv_rev]
  rw [h]
  exact Set.mul_mem_mul (H.data.Bopp.inv_mem hc) (H.data.B.inv_mem hb)

private lemma coefficient_zero_of_dense
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (l : Module.Dual k V) (v : V) {Z : Set (Variety.Point K)}
    (hZ : Dense Z) (h : ∀ g ∈ Z, l ((rho.action g).1 v) = 0) :
    ∀ g, l ((rho.action g).1 v) = 0 := by
  obtain ⟨e, f, hf⟩ := hrho
  let q := rationalRepresentationLinearMatrixCoefficient rho e f l v
  have hq (g) : q g = l ((rho.action g).1 v) :=
    rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l v g
  have hc : IsClosed {g : Variety.Point K | q g = 0} := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    obtain ⟨p, hp⟩ := q.representedBy
    refine ⟨{p}, ?_⟩
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    rw [← hp g]
  have hsub : Z ⊆ {g : Variety.Point K | q g = 0} := by
    intro g hg
    rw [Set.mem_ofPred_eq, hq]
    exact h g hg
  intro g
  rw [← hq]
  exact closure_minimal hsub hc (hZ g)

omit [FiniteDimensional k V] in
/-- Every nonzero functional separates the full point-group orbit of every
nonzero vector in a rational irreducible representation. -/
public theorem matrixCoefficient_separates_irreducible
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (l : Module.Dual k V) (hl : l ≠ 0) (v : V)
    (h : ∀ g, l ((rho.action g).1 v) = 0) : v = 0 := by
  let W : Submodule k V := ⨅ g : Variety.Point K, LinearMap.ker (l.comp (rho.action g).1)
  have hW : IsInvariantSubmodule rho W := by
    intro g x hx
    rw [Submodule.mem_iInf] at hx ⊢
    intro t
    have ht := hx (t * g)
    change l ((rho.action t).1 ((rho.action g).1 x)) = 0
    simpa [map_mul] using ht
  have hvW : v ∈ W := by rw [Submodule.mem_iInf]; exact h
  rcases hirr.2 W hW with hb | ht
  · simpa [hb] using hvW
  · apply False.elim
    apply hl
    ext x
    have hxW : x ∈ W := ht ▸ Submodule.mem_top
    rw [Submodule.mem_iInf] at hxW
    simpa using hxW 1

private lemma positive_fixed_pairing_separates
    (H : OppositeBorelBigCell T D P)
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (tau : RationalRepresentation K (Module.Dual k V))
    (htau : IsDualRepresentation rho tau)
    (l : Module.Dual k V) (hl : GeneratesInvariantLine tau H.data.Bopp l)
    (w : V) (hw : ∀ g ∈ RootSubgroupGenerated D P, (rho.action g).1 w = w)
    (hlw : l w = 0) : w = 0 := by
  apply matrixCoefficient_separates_irreducible rho hirr l hl.1 w
  apply coefficient_zero_of_dense rho hirr.1 l w (reverseCell_dense H)
  intro g hg
  obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.mp hg
  obtain ⟨t, u, ht, hu, rfl⟩ := (H.positive_decomposition b).mp hb
  have hct : c * t ∈ H.data.Bopp := H.data.Bopp.mul_mem hc (H.torus_le_negative ht)
  obtain ⟨d, hd⟩ := hl.2 (c * t)⁻¹ (H.data.Bopp.inv_mem hct)
  have heval := htau (c * t)⁻¹ l w
  rw [hd] at heval
  have heq : l ((rho.action (c * t)).1 w) = d • l w := by
    simpa using heval.symm
  rw [← mul_assoc, map_mul]
  change l ((rho.action (c * t)).1 ((rho.action u).1 w)) = 0
  rw [hw u hu, heq, hlw, smul_zero]

/-- An opposite highest vector in the dual has inverse character and pairs
nontrivially with the chosen highest vector. -/
public theorem exists_opposite_dual_highestWeight
    (H : OppositeBorelBigCell T D P) (hT : IsMaximalTorus T)
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (v : V) (chi : TorusWeight T) (hv : HasHighWeight rho H.data.B T v chi)
    (tau : RationalRepresentation K (Module.Dual k V))
    (htau : IsDualRepresentation rho tau) (htaur : IsRationalRepresentation tau) :
    ∃ l : Module.Dual k V,
      HasHighWeight tau H.data.Bopp T l chi⁻¹ ∧ l v ≠ 0 := by
  let : Nontrivial V := ⟨⟨v, 0, hv.1.1⟩⟩
  obtain ⟨l, nu, hl⟩ := highWeight_exists_of_borel H.data.Bopp T tau htaur
    H.data.Bopp_isBorel hT H.torus_le_negative
  have hvfix : ∀ g ∈ RootSubgroupGenerated D P, (rho.action g).1 v = v := by
    intro g hg
    apply invariantLine_fixed_of_unipotent_subgroup rho hirr.1 H.data.B
      H.data.positive_witness.unipotent v hv.1 H.data.positive_witness.radical.1
      H.data.positive_witness.radical.2.1 g
    rwa [← H.data.positive_witness.root_generated] at hg
  have hlv : l v ≠ 0 := fun h => hv.1.1
    (positive_fixed_pairing_separates H rho hirr tau htau l hl.1 v hvfix h)
  refine ⟨l, ⟨hl.1, hl.1.1, ?_⟩, hlv⟩
  intro t
  have hchar : nu.pointCharacter t = (chi⁻¹).pointCharacter t := by
    apply mul_right_cancel₀ hlv
    have h := htau (T.includePoint t) l v
    rw [hl.2.2 t] at h
    have hinv : (T.includePoint t)⁻¹ = T.includePoint t⁻¹ := rfl
    rw [hinv, hv.2.2 t⁻¹, map_smul] at h
    have hpoint : chi.pointCharacter t⁻¹ = (chi⁻¹).pointCharacter t := by
      change (dPointEquiv 1 (chi.onPoints t⁻¹) 0 : k) =
        (dPointEquiv 1 (chi.onPoints t)⁻¹ 0 : k)
      rw [map_inv]
    simpa only [LinearMap.smul_apply, smul_eq_mul, hpoint] using h
  rw [hl.2.2 t, hchar]

/-- Full algebraic positive-unipotent invariants lie on the highest line.
No restricted-weight or finite-group hypothesis occurs in this theorem. -/
public theorem fixed_positiveRoots_mem_highestLine
    (H : OppositeBorelBigCell T D P) (hT : IsMaximalTorus T)
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (v : V) (chi : TorusWeight T) (hv : HasHighWeight rho H.data.B T v chi)
    (w : V) (hw : ∀ g ∈ RootSubgroupGenerated D P, (rho.action g).1 w = w) :
    w ∈ Submodule.span k ({v} : Set V) := by
  let : Nontrivial V := ⟨⟨v, 0, hv.1.1⟩⟩
  obtain ⟨tau, htau, htaur⟩ := rationalRepresentation_dual_exists rho hirr.1
  obtain ⟨l, nu, hl⟩ := highWeight_exists_of_borel H.data.Bopp T tau htaur
    H.data.Bopp_isBorel hT H.torus_le_negative
  have hvfix : ∀ g ∈ RootSubgroupGenerated D P, (rho.action g).1 v = v := by
    intro g hg
    apply invariantLine_fixed_of_unipotent_subgroup rho hirr.1 H.data.B
      H.data.positive_witness.unipotent v hv.1 H.data.positive_witness.radical.1
      H.data.positive_witness.radical.2.1 g
    rwa [← H.data.positive_witness.root_generated] at hg
  have hlv : l v ≠ 0 := fun h => hv.1.1
    (positive_fixed_pairing_separates H rho hirr tau htau l hl.1 v hvfix h)
  have hzero : l v • w - l w • v = 0 := by
    apply positive_fixed_pairing_separates H rho hirr tau htau l hl.1
    · intro g hg
      simp only [map_sub, map_smul, hw g hg, hvfix g hg]
    · simp [mul_comm]
  apply (Submodule.mem_span_singleton).mpr
  refine ⟨l w / l v, ?_⟩
  have heq := congrArg (fun x : V => (l v)⁻¹ • x) (sub_eq_zero.mp hzero)
  simpa [smul_smul, hlv, div_eq_mul_inv, mul_comm] using heq.symm

/-- The full opposite-unipotent orbit of a highest vector spans its rational
irreducible representation. This is an algebraic orbit, not a finite orbit. -/
public theorem span_negativeRoots_orbit_eq_top
    (H : OppositeBorelBigCell T D P)
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (v : V) (hv : GeneratesInvariantLine rho H.data.B v) :
    Submodule.span k (Set.range (fun g : RootSubgroupGenerated D (D.neg ⁻¹' P) =>
      (rho.action g.val).1 v)) = ⊤ := by
  by_contra hne
  obtain ⟨l, hl, hker⟩ := (Submodule.span k (Set.range
    (fun g : RootSubgroupGenerated D (D.neg ⁻¹' P) => (rho.action g.val).1 v))).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hne)
  have hz : ∀ u ∈ RootSubgroupGenerated D (D.neg ⁻¹' P),
      l ((rho.action u).1 v) = 0 := by
    intro u hu
    exact hker (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)
  apply hv.1
  apply matrixCoefficient_separates_irreducible rho hirr l hl v
  apply coefficient_zero_of_dense rho hirr.1 l v (reverseCell_dense H)
  intro g hg
  obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.mp hg
  obtain ⟨t, u, ht, hu, hcu⟩ := (H.negative_decomposition c).mp hc
  have huU : u ∈ H.data.opposite_witness.unipotent := by
    rwa [← H.data.opposite_witness.root_generated] at hu
  have hconj : t * u * t⁻¹ ∈ RootSubgroupGenerated D (D.neg ⁻¹' P) := by
    rw [← H.data.opposite_witness.root_generated]
    exact H.data.opposite_witness.radical.2.2.1 t (H.torus_le_negative ht) u huU
  have htb : t * b ∈ H.data.B := H.data.B.mul_mem (H.torus_le_positive ht) hb
  obtain ⟨d, hd⟩ := hv.2 (t * b) htb
  have heq : c * b = (t * u * t⁻¹) * (t * b) := by rw [hcu]; group
  rw [heq, map_mul]
  change l ((rho.action (t * u * t⁻¹)).1 ((rho.action (t * b)).1 v)) = 0
  rw [hd, map_smul, map_smul, hz _ hconj, smul_zero]

end Theory.AlgebraicGroup
