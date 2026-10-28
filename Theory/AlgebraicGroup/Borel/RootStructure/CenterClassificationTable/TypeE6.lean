module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4
public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Cartan.Kernels
public import Theory.AlgebraicGroup.RootData.Chevalley
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
The type `E₆` center calculation in the GLS3 center table.  The six Cartan
relations have a cyclic kernel of order three: in the displayed numbering the
coordinates are `(ω, ω², 1, 1, ω, ω²)`.  The explicit kernel equivalence is
the complete lattice calculation.  The geometric center/weight-lattice
identification is kept as a hypothesis at this boundary, so this module does
not depend on the unresolved global center theorem.

The module also exports a placeholder-free quotient-character bridge conditional
on a coherent integral coordinate witness: the witness contains a
fundamental-weight basis, the standard Cartan columns for simple roots, and
root-lattice containment.  The global construction of that witness from
semantic universality is tracked separately because the current
root-system model API is real-linear only.

The final transfer lemmas turn either a center-to-kernel equivalence (for the
universal version) or a surjective kernel-to-center morphism (for an arbitrary
version) into the public center-shape predicates.  For the latter, the module
also constructs the required surjection from an isogeny out of a universal
version: the connected-isogeny center theorem maps the universal center onto
the target center.
-/

universe u

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The common multiplicative kernel of the standard type-`E₆` Cartan
relations on six coordinate units. -/
@[expose]
public def e6CartanRelationKernel : Subgroup (Fin 6 → kˣ) where
  carrier := {t | ∀ j,
    (∏ i, t i ^ dynkinCartanEntry ⟨.E6, 6⟩ i j) = 1}
  one_mem' := by
    intro j
    simp
  mul_mem' := by
    intro a b ha hb j
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp_rw [Pi.mul_apply, mul_zpow]
    rw [Finset.prod_mul_distrib]
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha j
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp_rw [Pi.inv_apply, inv_zpow]
    rw [Finset.prod_inv_distrib, ha, inv_one]

/-- The cyclic order-three parameter in the Cartan kernel. -/
@[expose]
public def e6CartanRelationKernelMap : rootsOfUnity 3 k →*
    e6CartanRelationKernel (k := k) := by
  let f : rootsOfUnity 3 k →* (Fin 6 → kˣ) :=
    { toFun := fun ω i =>
        if i.val = 0 then ω
        else if i.val = 1 then ω ^ (2 : ℤ)
        else if i.val = 4 then ω
        else if i.val = 5 then ω ^ (2 : ℤ)
        else 1
      map_one' := by
        ext i
        fin_cases i <;> simp
      map_mul' := by
        intro ω ζ
        funext i
        fin_cases i <;> simp [mul_pow] }
  exact f.codRestrict e6CartanRelationKernel (by
    intro ω j
    have hω3 : (ω : kˣ) ^ (3 : ℕ) = 1 :=
      (mem_rootsOfUnity 3 (ω : kˣ)).mp ω.property
    have h1 : (ω : kˣ)⁻¹ * ((ω : kˣ) ^ (2 : ℕ)) ^ 2 = 1 := by
      calc
        (ω : kˣ)⁻¹ * ((ω : kˣ) ^ (2 : ℕ)) ^ 2 = (ω : kˣ) ^ 3 := by group
        _ = 1 := hω3
    have h2 : ((ω : kˣ) ^ (2 : ℕ))⁻¹ * (ω : kˣ)⁻¹ = 1 := by
      calc
        ((ω : kˣ) ^ (2 : ℕ))⁻¹ * (ω : kˣ)⁻¹ = ((ω : kˣ) ^ 3)⁻¹ := by group
        _ = 1 := by rw [hω3, inv_one]
    fin_cases j <;>
      simp [f, dynkinCartanEntry, Fin.prod_univ_succ, zpow_ofNat, h1, h2])

@[simp]
public lemma e6CartanRelationKernelMap_apply
    (ω : rootsOfUnity 3 k) (i : Fin 6) :
    (e6CartanRelationKernelMap ω).1 i =
      if i.val = 0 then ω
      else if i.val = 1 then ω ^ (2 : ℤ)
      else if i.val = 4 then ω
      else if i.val = 5 then ω ^ (2 : ℤ)
      else 1 := by
  change (if i.val = 0 then (ω : kˣ)
    else if i.val = 1 then (ω : kˣ) ^ (2 : ℤ)
    else if i.val = 4 then (ω : kˣ)
    else if i.val = 5 then (ω : kˣ) ^ (2 : ℤ)
    else 1) = _
  fin_cases i <;> rfl

public lemma e6CartanRelationKernelMap_injective :
    Function.Injective (e6CartanRelationKernelMap (k := k)) := by
  intro ω ζ h
  have h0 := congrArg (fun t => t.1 (0 : Fin 6)) h
  simpa [e6CartanRelationKernelMap_apply] using h0

public lemma e6CartanRelationKernelMap_surjective :
    Function.Surjective (e6CartanRelationKernelMap (k := k)) := by
  intro t
  rcases dynkinCartanRelationKernel_E6 t.1 (fun j => t.2 j) with
    ⟨ω, hω, h0, h1, h2, h3, h4, h5⟩
  let ω' : rootsOfUnity 3 k :=
    ⟨ω, by simpa [mem_rootsOfUnity] using hω⟩
  refine ⟨ω', ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · simpa [e6CartanRelationKernelMap_apply, ω'] using h0.symm
  · simpa [e6CartanRelationKernelMap_apply, ω'] using h1.symm
  · simpa [e6CartanRelationKernelMap_apply, ω'] using h2.symm
  · simpa [e6CartanRelationKernelMap_apply, ω'] using h3.symm
  · simpa [e6CartanRelationKernelMap_apply, ω'] using h4.symm
  · simpa [e6CartanRelationKernelMap_apply, ω'] using h5.symm

/-- The explicit identification of the type-`E₆` Cartan kernel with the
order-three roots of unity. -/
public noncomputable def e6CartanRelationKernelEquiv :
    rootsOfUnity 3 k ≃* e6CartanRelationKernel (k := k) :=
  MulEquiv.ofBijective e6CartanRelationKernelMap
    ⟨e6CartanRelationKernelMap_injective,
      e6CartanRelationKernelMap_surjective⟩

section E6CharacterLattice

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure E6TorusCharacterCoordinates
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T) where
  simpleRoot : Fin 6 ≃ {alpha : D.Root // alpha ∈ D.simple}
  characterBasis : Module.Basis (Fin 6) ℤ (Additive (TorusWeight T))
  rootWeight_eq_cartanColumn : ∀ j,
    D.rootWeight (simpleRoot j).1 =
      ∏ i, Additive.toMul (characterBasis i) ^
        dynkinCartanEntry ⟨.E6, 6⟩ i j
  rootWeight_mem_simpleRootLattice : ∀ alpha,
    D.rootWeight alpha ∈ Subgroup.closure
      (Set.range (fun j : Fin 6 => D.rootWeight (simpleRoot j).1))

private noncomputable def e6RawCharacter
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (b : Module.Basis (Fin 6) ℤ (Additive (TorusWeight T)))
    (t : Fin 6 → kˣ) : TorusWeight T →* kˣ where
  toFun := fun chi => ∏ i, t i ^ (b.repr (Additive.ofMul chi)) i
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
private lemma e6RawCharacter_apply_basisProduct
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (b : Module.Basis (Fin 6) ℤ (Additive (TorusWeight T)))
    (t : Fin 6 → kˣ) (c : Fin 6 → ℤ) :
    e6RawCharacter T b t
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
private lemma e6RawCharacter_eq_one_of_simpleRootLattice
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (C : E6TorusCharacterCoordinates T D)
    (t : Fin 6 → kˣ) (chi : TorusWeight T)
    (hchi : chi ∈ Subgroup.closure
      (Set.range (fun j : Fin 6 => D.rootWeight (C.simpleRoot j).1)))
    (ht : t ∈ e6CartanRelationKernel (k := k)) :
    e6RawCharacter T C.characterBasis t chi = 1 := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hchi
  · intro chi hchi
    rcases hchi with ⟨j, rfl⟩
    change e6RawCharacter T C.characterBasis t
      (D.rootWeight (C.simpleRoot j).1) = 1
    rw [show D.rootWeight (C.simpleRoot j).1 =
      ∏ i, Additive.toMul (C.characterBasis i) ^
        dynkinCartanEntry ⟨.E6, 6⟩ i j from C.rootWeight_eq_cartanColumn j]
    exact (e6RawCharacter_apply_basisProduct T C.characterBasis t _).trans
      (ht j)
  · simp
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]
    simp
  · intro a _ ha
    rw [map_inv, ha]
    simp

private noncomputable def e6QuotientCharacterToKernel
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E6TorusCharacterCoordinates T D) :
    ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) →*
      e6CartanRelationKernel (k := k) where
  toFun := fun phi =>
    ⟨fun i => phi (QuotientGroup.mk' (TorusRootLattice T)
      (Additive.toMul (C.characterBasis i))), by
      intro j
      change ∏ i, phi (QuotientGroup.mk' (TorusRootLattice T)
        (Additive.toMul (C.characterBasis i))) ^
          dynkinCartanEntry ⟨.E6, 6⟩ i j = 1
      calc
        _ = phi (QuotientGroup.mk' (TorusRootLattice T)
              (∏ i, Additive.toMul (C.characterBasis i) ^
                dynkinCartanEntry ⟨.E6, 6⟩ i j)) := by
          rw [map_prod (QuotientGroup.mk' (TorusRootLattice T))]
          rw [map_prod]
          simp only [map_zpow]
        _ = phi (QuotientGroup.mk' (TorusRootLattice T)
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
    intro phi psi
    ext i
    simp

private noncomputable def e6KernelToQuotientCharacter
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E6TorusCharacterCoordinates T D) :
    e6CartanRelationKernel (k := k) →*
      ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) where
  toFun := fun t => QuotientGroup.lift (TorusRootLattice T)
    (e6RawCharacter T C.characterBasis t.1) (by
      intro chi hchi
      rw [TorusRootLattice] at hchi
      rw [← hD.2.1] at hchi
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hchi
      · intro chi hchi
        rcases hchi with ⟨alpha, rfl⟩
        exact e6RawCharacter_eq_one_of_simpleRootLattice T D C t.1
          (D.rootWeight alpha) (C.rootWeight_mem_simpleRootLattice alpha) t.2
      · simp
      · intro a b _ _ ha hb
        change e6RawCharacter T C.characterBasis t.1 (a * b) = 1
        rw [map_mul, ha, hb]
        simp
      · intro a _ ha
        change e6RawCharacter T C.characterBasis t.1 a⁻¹ = 1
        rw [map_inv, ha]
        simp)
  map_one' := by
    apply QuotientGroup.monoidHom_ext
    ext chi
    simp [e6RawCharacter]
  map_mul' := by
    intro t s
    apply MonoidHom.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro chi
    change e6RawCharacter T C.characterBasis (t * s).1 chi =
      e6RawCharacter T C.characterBasis t.1 chi *
        e6RawCharacter T C.characterBasis s.1 chi
    change (∏ x, (t.1 x * s.1 x) ^
      (C.characterBasis.repr (Additive.ofMul chi)) x) = _
    simp_rw [mul_zpow]
    rw [Finset.prod_mul_distrib]
    rfl

public noncomputable def e6QuotientCharacterToCartanKernel
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E6TorusCharacterCoordinates T D) :
    ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) →*
      e6CartanRelationKernel (k := k) :=
  e6QuotientCharacterToKernel T D hD C

public noncomputable def e6CartanKernelToQuotientCharacter
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E6TorusCharacterCoordinates T D) :
    e6CartanRelationKernel (k := k) →*
      ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) :=
  e6KernelToQuotientCharacter T D hD C

omit [IsAlgClosed k] in
public theorem e6QuotientCharacterToCartanKernel_bijective
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E6TorusCharacterCoordinates T D) :
    Function.Bijective (e6QuotientCharacterToCartanKernel T D hD C) := by
  constructor
  · intro phi psi h
    have hcoord : ∀ i, phi (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) =
        psi (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) := by
      intro i
      have hi := congrFun (congrArg Subtype.val h) i
      change phi (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) =
        psi (QuotientGroup.mk' (TorusRootLattice T)
          (Additive.toMul (C.characterBasis i))) at hi
      exact hi
    apply MonoidHom.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro chi
    have hchi : chi = ∏ i,
        Additive.toMul (C.characterBasis i) ^
          (C.characterBasis.repr (Additive.ofMul chi)) i := by
      apply Additive.ofMul.injective
      simp
    rw [hchi]
    let L := TorusRootLattice T
    let coeff : Fin 6 → ℤ :=
      fun i => (C.characterBasis.repr (Additive.ofMul chi)) i
    have hprod :
        QuotientGroup.mk' L (∏ i, Additive.toMul (C.characterBasis i) ^ coeff i) =
          ∏ i, (QuotientGroup.mk' L
            (Additive.toMul (C.characterBasis i))) ^ coeff i := by
      rw [map_prod (QuotientGroup.mk' L)]
      simp only [map_zpow]
    change phi (QuotientGroup.mk' L
      (∏ i, Additive.toMul (C.characterBasis i) ^ coeff i)) =
      psi (QuotientGroup.mk' L
        (∏ i, Additive.toMul (C.characterBasis i) ^ coeff i))
    rw [hprod, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_zpow, map_zpow, hcoord i]
  · intro q
    let phi := e6CartanKernelToQuotientCharacter T D hD C q
    refine ⟨phi, ?_⟩
    apply Subtype.ext
    funext i
    change (e6CartanKernelToQuotientCharacter T D hD C q)
      (QuotientGroup.mk' (TorusRootLattice T)
        (Additive.toMul (C.characterBasis i))) = q.1 i
    change e6RawCharacter T C.characterBasis q.1
      (Additive.toMul (C.characterBasis i)) = q.1 i
    simp [e6RawCharacter, Finsupp.single_apply]

omit [IsAlgClosed k] in
public theorem e6QuotientCharacterCartanKernelEquiv_nonempty
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E6TorusCharacterCoordinates T D) :
    Nonempty (((TorusWeight T ⧸ TorusRootLattice T) →* kˣ) ≃*
      e6CartanRelationKernel (k := k)) := by
  exact ⟨MulEquiv.ofBijective
    (e6QuotientCharacterToCartanKernel T D hD C)
    (e6QuotientCharacterToCartanKernel_bijective T D hD C)⟩

end E6CharacterLattice


/-- A center/kernel identification gives the universal `E₆` center shape. -/
public theorem e6_hasCenterShape_of_centerRelationKernelEquiv
    {K : Variety k} [AlgebraicGroup K]
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        e6CartanRelationKernel (k := k))) :
    HasCenterShape (K := K) (.rootsOfUnity 3) := by
  simpa only [HasCenterShape] using
    Nonempty.map
      (fun e => e.trans (e6CartanRelationKernelEquiv (k := k)).symm)
      hCenter

/-- A surjective map from the Cartan kernel gives the arbitrary-version
homomorphic-image conclusion. -/
public theorem e6_isCenterHomomorphicImage_of_centerRelationKernel
    {K : Variety k} [AlgebraicGroup K]
    (hImage : ∃ f : e6CartanRelationKernel (k := k) →*
        Subgroup.center (Variety.Point K), Function.Surjective f) :
    IsCenterHomomorphicImageOfShape (K := K) (.rootsOfUnity 3) := by
  rcases hImage with ⟨f, hf⟩
  refine ⟨f.comp (e6CartanRelationKernelMap (k := k)), ?_⟩
  intro z
  obtain ⟨u, hu⟩ := hf z
  obtain ⟨t, ht⟩ := e6CartanRelationKernelMap_surjective u
  refine ⟨t, ?_⟩
  change f (e6CartanRelationKernelMap t) = z
  rw [ht, hu]

/-- An isogeny from a universal version transports its Cartan-kernel center
identification onto the center of the target version. -/
public theorem e6_centerRelationKernel_surjects_of_isogeny
    {K Ku : Variety k} [AlgebraicGroup K] [AlgebraicGroup Ku]
    (hKu : IsUniversalVersion Ku)
    (phi : AlgebraicGroup.Morphism Ku K) (hphi : IsIsogeny phi)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point Ku) ≃*
        e6CartanRelationKernel (k := k))) :
    ∃ f : e6CartanRelationKernel (k := k) →*
        Subgroup.center (Variety.Point K), Function.Surjective f := by
  obtain ⟨centerEquiv⟩ := hCenter
  exact center_homomorphic_image_of_isogeny phi hphi hKu.1.1
    centerEquiv.symm

/-- Universal-version wrapper for the type-`E₆` leaf.  The root-system
hypotheses identify the relevant lattice; `hCenter` is the explicit
center-to-kernel transfer supplied by the geometric center-character layer. -/
public theorem typeE6_universal_center_shape_core
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.E6, 6⟩)
    (_hUniversal : IsUniversalVersion K)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        e6CartanRelationKernel (k := k))) :
    HasCenterShape (K := K) (universalCenterShape ⟨.E6, 6⟩) := by
  simpa [universalCenterShape] using
    e6_hasCenterShape_of_centerRelationKernelEquiv hCenter

/-- Arbitrary-version wrapper for the type-`E₆` leaf.  `hImage` is the
center morphism supplied by the universal-cover/isogeny transfer layer. -/
public theorem typeE6_center_homomorphic_image_core
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.E6, 6⟩)
    (hImage : ∃ f : e6CartanRelationKernel (k := k) →*
        Subgroup.center (Variety.Point K), Function.Surjective f) :
    IsCenterHomomorphicImageOfShape (K := K)
      (universalCenterShape ⟨.E6, 6⟩) := by
  simpa [universalCenterShape] using
    e6_isCenterHomomorphicImage_of_centerRelationKernel hImage

end Theory.AlgebraicGroup
