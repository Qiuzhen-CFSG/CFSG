module

public import Theory.AlgebraicGroup.Borel.RootStructure.CenterClassificationTable.TypeE7Universal
public import Theory.AlgebraicGroup.RootData.Chevalley

/-!
This module supplies the integral coordinate bridge needed to identify the
universal `E₇` center with the explicit Cartan-relation kernel.  The input
`E7TorusCharacterCoordinates` records a numbered simple-root basis, a
fundamental-weight basis of the torus character lattice, the Cartan-column
coordinates of every simple root, and the fact that all realized roots lie in
the simple-root lattice.  The first three fields are the based integral
root-datum/weight equivalence; the final field is the transport assertion
needed to descend a character through the root lattice quotient.

The proof constructs mutually inverse multiplicative homomorphisms.  A
quotient character is evaluated on the seven basis weights to obtain the
Cartan coordinates, while a Cartan-kernel point is extended by the basis
coordinate formula.  The Cartan equations make the first map land in the
kernel, and the root-lattice hypothesis makes the second map descend.  Basis
coordinates then prove both inverse statements without using classification
theorems or placeholder declarations.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure E7TorusCharacterCoordinates
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T) where
  simpleRoot : Fin 7 ≃ {alpha : D.Root // alpha ∈ D.simple}
  characterBasis : Module.Basis (Fin 7) ℤ (Additive (TorusWeight T))
  rootWeight_eq_cartanColumn : ∀ j,
    D.rootWeight (simpleRoot j).1 =
      ∏ i, Additive.toMul (characterBasis i) ^
        dynkinCartanEntry ⟨.E7, 7⟩ i j
  rootWeight_mem_simpleRootLattice : ∀ α,
    D.rootWeight α ∈ Subgroup.closure
      (Set.range (fun j : Fin 7 => D.rootWeight (simpleRoot j).1))

private noncomputable def rawCharacter
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (b : Module.Basis (Fin 7) ℤ (Additive (TorusWeight T)))
    (t : Fin 7 → kˣ) : TorusWeight T →* kˣ where
  toFun := fun χ => ∏ i, t i ^ (b.repr (Additive.ofMul χ)) i
  map_one' := by simp
  map_mul' := by
    intro x y
    have hrepr : b.repr (Additive.ofMul (x * y)) =
        b.repr (Additive.ofMul x) + b.repr (Additive.ofMul y) := by
      change b.repr (Additive.ofMul x + Additive.ofMul y) = _
      rw [map_add]
    rw [hrepr]
    simp_rw [Finsupp.add_apply, zpow_add]
    rw [Finset.prod_mul_distrib]

omit [IsAlgClosed k] in
private lemma rawCharacter_apply_basisProduct
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (b : Module.Basis (Fin 7) ℤ (Additive (TorusWeight T)))
    (t : Fin 7 → kˣ) (c : Fin 7 → ℤ) :
    rawCharacter T b t
      (∏ i, Additive.toMul (b i) ^ c i) = ∏ i, t i ^ c i := by
  change ∏ i, t i ^ (b.repr (Additive.ofMul
    (∏ i, Additive.toMul (b i) ^ c i))) i = _
  have hrepr : b.repr (Additive.ofMul
      (∏ i, Additive.toMul (b i) ^ c i)) =
      Finsupp.equivFunOnFinite.symm c := by
    apply Finsupp.ext
    intro i
    simp [Finsupp.equivFunOnFinite, Finsupp.single_apply]
    rfl
  rw [hrepr]
  rfl

omit [IsAlgClosed k] in
private lemma rawCharacter_eq_one_of_simpleRootLattice
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (C : E7TorusCharacterCoordinates T D)
    (t : Fin 7 → kˣ) (χ : TorusWeight T)
    (hχ : χ ∈ Subgroup.closure
      (Set.range (fun j : Fin 7 => D.rootWeight (C.simpleRoot j).1)))
    (ht : t ∈ e7CartanRelationKernel (k := k)) :
    rawCharacter T C.characterBasis t χ = 1 := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hχ
  · intro χ hχ
    rcases hχ with ⟨j, rfl⟩
    change rawCharacter T C.characterBasis t (D.rootWeight (C.simpleRoot j).1) = 1
    rw [show D.rootWeight (C.simpleRoot j).1 =
      ∏ i, Additive.toMul (C.characterBasis i) ^
        dynkinCartanEntry ⟨.E7, 7⟩ i j from C.rootWeight_eq_cartanColumn j]
    exact (rawCharacter_apply_basisProduct T C.characterBasis t _).trans
      (ht j)
  · simp
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]
    simp
  · intro a _ ha
    rw [map_inv, ha]
    simp

private noncomputable def quotientCharacterToKernel
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E7TorusCharacterCoordinates T D) :
    ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) →*
      e7CartanRelationKernel (k := k) where
  toFun := fun φ =>
    ⟨fun i => φ (QuotientGroup.mk' (TorusRootLattice T)
      (Additive.toMul (C.characterBasis i))), by
      intro j
      change ∏ i, φ (QuotientGroup.mk' (TorusRootLattice T)
        (Additive.toMul (C.characterBasis i))) ^
          dynkinCartanEntry ⟨.E7, 7⟩ i j = 1
      calc
        _ = φ (QuotientGroup.mk' (TorusRootLattice T)
              (∏ i, Additive.toMul (C.characterBasis i) ^
                dynkinCartanEntry ⟨.E7, 7⟩ i j)) := by
          rw [map_prod (QuotientGroup.mk' (TorusRootLattice T))]
          rw [map_prod]
          simp only [map_zpow]
        _ = φ (QuotientGroup.mk' (TorusRootLattice T)
              (D.rootWeight (C.simpleRoot j).1)) := by
          rw [C.rootWeight_eq_cartanColumn j]
        _ = 1 := by
          have hroot : D.rootWeight (C.simpleRoot j).1 ∈ TorusRootLattice T := by
            apply Subgroup.subset_closure
            rw [← hD.2.1]
            exact Set.mem_range_self (C.simpleRoot j).1
          have hq : QuotientGroup.mk' (TorusRootLattice T)
              (D.rootWeight (C.simpleRoot j).1) = 1 :=
            (QuotientGroup.eq_one_iff _).2 hroot
          simp [hq]
        ⟩
  map_one' := by
    ext i
    simp
  map_mul' := by
    intro φ ψ
    ext i
    simp

private noncomputable def kernelToQuotientCharacter
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E7TorusCharacterCoordinates T D) :
    e7CartanRelationKernel (k := k) →*
      ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) where
  toFun := fun t => QuotientGroup.lift (TorusRootLattice T)
    (rawCharacter T C.characterBasis t.1) (by
      intro χ hχ
      rw [TorusRootLattice] at hχ
      rw [← hD.2.1] at hχ
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hχ
      · intro χ hχ
        rcases hχ with ⟨α, rfl⟩
        exact rawCharacter_eq_one_of_simpleRootLattice T D C t.1
          (D.rootWeight α) (C.rootWeight_mem_simpleRootLattice α) t.2
      · simp
      · intro a b _ _ ha hb
        change rawCharacter T C.characterBasis t.1 (a * b) = 1
        rw [map_mul, ha, hb]
        simp
      · intro a _ ha
        change rawCharacter T C.characterBasis t.1 a⁻¹ = 1
        rw [map_inv, ha]
        simp)
  map_one' := by
    apply QuotientGroup.monoidHom_ext
    ext χ
    simp [rawCharacter]
  map_mul' := by
    intro t s
    apply MonoidHom.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro χ
    change rawCharacter T C.characterBasis (t * s).1 χ =
      rawCharacter T C.characterBasis t.1 χ *
        rawCharacter T C.characterBasis s.1 χ
    change (∏ x, (t.1 x * s.1 x) ^
      (C.characterBasis.repr (Additive.ofMul χ)) x) = _
    simp_rw [mul_zpow]
    rw [Finset.prod_mul_distrib]
    rfl

public noncomputable def e7QuotientCharacterToCartanKernel
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E7TorusCharacterCoordinates T D) :
    ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) →*
      e7CartanRelationKernel (k := k) :=
  quotientCharacterToKernel T D hD C

public noncomputable def e7CartanKernelToQuotientCharacter
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E7TorusCharacterCoordinates T D) :
    e7CartanRelationKernel (k := k) →*
      ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) :=
  kernelToQuotientCharacter T D hD C

omit [IsAlgClosed k] in
public theorem e7QuotientCharacterToCartanKernel_bijective
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E7TorusCharacterCoordinates T D) :
    Function.Bijective (e7QuotientCharacterToCartanKernel T D hD C) := by
  constructor
  · intro φ ψ h
    have hcoord : ∀ i, φ (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) =
        ψ (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) := by
      intro i
      have hi := congrFun (congrArg Subtype.val h) i
      change φ (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) =
        ψ (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) at hi
      exact hi
    apply MonoidHom.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro χ
    have hχ : χ = ∏ i,
        Additive.toMul (C.characterBasis i) ^
          (C.characterBasis.repr (Additive.ofMul χ)) i := by
      apply Additive.ofMul.injective
      simp
    rw [hχ]
    let L := TorusRootLattice T
    let coeff : Fin 7 → ℤ :=
      fun i => (C.characterBasis.repr (Additive.ofMul χ)) i
    have hprod :
        QuotientGroup.mk' L (∏ i, Additive.toMul (C.characterBasis i) ^ coeff i) =
          ∏ i, (QuotientGroup.mk' L (Additive.toMul (C.characterBasis i))) ^ coeff i := by
      rw [map_prod (QuotientGroup.mk' L)]
      simp only [map_zpow]
    change φ (QuotientGroup.mk' L
      (∏ i, Additive.toMul (C.characterBasis i) ^ coeff i)) =
      ψ (QuotientGroup.mk' L
        (∏ i, Additive.toMul (C.characterBasis i) ^ coeff i))
    rw [hprod, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_zpow, map_zpow, hcoord i]
  · intro q
    let φ := e7CartanKernelToQuotientCharacter T D hD C q
    refine ⟨φ, ?_⟩
    apply Subtype.ext
    funext i
    change (e7CartanKernelToQuotientCharacter T D hD C q)
      (QuotientGroup.mk' (TorusRootLattice T)
        (Additive.toMul (C.characterBasis i))) = q.1 i
    change rawCharacter T C.characterBasis q.1
      (Additive.toMul (C.characterBasis i)) = q.1 i
    simp [rawCharacter, Finsupp.single_apply]

omit [IsAlgClosed k] in
public theorem e7QuotientCharacterCartanKernelEquiv_nonempty
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E7TorusCharacterCoordinates T D) :
    Nonempty (((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) ≃*
      e7CartanRelationKernel (k := k)) := by
  exact ⟨MulEquiv.ofBijective
    (e7QuotientCharacterToCartanKernel T D hD C)
    (e7QuotientCharacterToCartanKernel_bijective T D hD C)⟩

end Theory.AlgebraicGroup
