module
public import Theory.Character.ModularBlock.Cartan
public import Theory.Character.Inflation
public import Theory.Representation.Quotient

/-!
# Principal-block Cartan data under group isomorphism

Transport an arbitrary principal congruence datum along a group isomorphism,
retaining its exact cyclotomic root and prime ideal. Ordinary characters are
pulled back along the inverse isomorphism. Conjugacy-class cardinalities are
unchanged, so their central characters have identical reductions and their
principal congruence blocks have the same indices.

The complex selector coefficient formula and injectivity of the localization
map identify the localized selectors. Reduction at the unchanged prime then
identifies the actual splitting-field selectors. Pullback consequently
preserves block membership and the complete family of simple modules. Uniqueness
of odd-order root lifts compares genuine Brauer values and proves independence
of the transported family. Decomposition coefficients and hence every Cartan
entry are retained in both directions, without replacing the modular place.

This is the isomorphism invariance of the character-theoretic Cartan definition
in `Cartan.lean`, used for the concrete quotient computations in Fong,
*Some Sylow subgroups of order 32*, J. Algebra 6 (1967), p. 71, (6)–(7).
-/

public section
noncomputable section
namespace ModularBlock
open PrincipalBlockConstruction BlockPreliminaries BlockOrthogonality
open BrauerCoefficientExtension BrauerBlockReduction
open scoped BigOperators
universe u v
variable {G : Type u} {K : Type v} [Group G] [Finite G] [Group K] [Finite K]

private def classesEquiv (e : G ≃* K) : ConjClasses G ≃ ConjClasses K where
  toFun := ConjClasses.map e.toMonoidHom
  invFun := ConjClasses.map e.symm.toMonoidHom
  left_inv c := by
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    change ConjClasses.mk (e.symm (e g)) = _
    simp
  right_inv c := by
    obtain ⟨k, rfl⟩ := ConjClasses.exists_rep c
    change ConjClasses.mk (e (e.symm k)) = _
    simp

namespace PrincipalBlockConstruction.PrincipalCongruenceBlockData

/-- Transport the actual ordinary datum, retaining the root and prime ideal.
Reducibility keeps the index type, residue field and splitting field definitionally
identical to the original ones. The primitive-root order uses `Nat.card_congr`. -/
@[expose, reducible] def transport (d : PrincipalCongruenceBlockData G) (e : G ≃* K) :
    PrincipalCongruenceBlockData K where
  I := d.I
  fintypeI := d.fintypeI
  decidableEqI := d.decidableEqI
  chi i := d.chi i ∘ ConjClasses.map e.symm.toMonoidHom
  complete := by
    refine ⟨fun i => isIrreducibleConjCharacter_comp_surjective _ e.symm.surjective
      (d.complete.1 i), ?_, ?_⟩
    · intro χ hχ
      obtain ⟨i, hi⟩ := d.complete.2.1 (χ ∘ ConjClasses.map e.toMonoidHom)
        (isIrreducibleConjCharacter_comp_surjective _ e.surjective hχ)
      refine ⟨i, ?_⟩
      funext c
      obtain ⟨k, rfl⟩ := ConjClasses.exists_rep c
      have h := congrFun hi (ConjClasses.mk (e.symm k))
      change d.chi i (ConjClasses.mk (e.symm k)) = χ (ConjClasses.mk (e (e.symm k))) at h
      change d.chi i (ConjClasses.mk (e.symm k)) = χ (ConjClasses.mk k)
      simpa only [e.apply_symm_apply] using h
    · intro i j hij
      apply d.complete.2.2
      funext c
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
      have h := congrFun hij (ConjClasses.mk (e g))
      change d.chi i (ConjClasses.mk (e.symm (e g))) =
        d.chi j (ConjClasses.mk (e.symm (e g))) at h
      simpa only [e.symm_apply_apply] using h
  eta := d.eta
  eta_spec := (Nat.card_congr e.toEquiv) ▸ d.eta_spec
  primeIdeal := d.primeIdeal
  primeIdeal_maximal := d.primeIdeal_maximal
  primeIdeal_liesOverTwo := d.primeIdeal_liesOverTwo
  principal := d.principal
  principal_eq := by
    funext c
    change d.chi d.principal _ = 1
    rw [d.principal_eq]
    rfl

@[simp] theorem transport_eta (d : PrincipalCongruenceBlockData G) (e : G ≃* K) :
    (d.transport e).eta = d.eta := rfl

@[simp] theorem transport_primeIdeal (d : PrincipalCongruenceBlockData G) (e : G ≃* K) :
    (d.transport e).primeIdeal = d.primeIdeal := rfl

@[simp] theorem transport_chi (d : PrincipalCongruenceBlockData G) (e : G ≃* K)
    (i : d.I) (k : K) :
    (d.transport e).chi i (ConjClasses.mk k) = d.chi i (ConjClasses.mk (e.symm k)) := rfl

omit [Finite G] [Finite K] in
private theorem class_card (e : G ≃* K) (c : ConjClasses K) :
    Nat.card c.carrier = Nat.card ((classesEquiv e).symm c).carrier := by
  apply Nat.card_congr
  refine {
    toFun := fun k => ⟨e.symm k, ?_⟩
    invFun := fun g => ⟨e g, ?_⟩
    left_inv := fun k => Subtype.ext (e.apply_symm_apply k)
    right_inv := fun g => Subtype.ext (e.symm_apply_apply g) }
  · apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact congrArg (classesEquiv e).symm
      (ConjClasses.mem_carrier_iff_mk_eq.mp k.property)
  · apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    have h := congrArg (classesEquiv e)
      (ConjClasses.mem_carrier_iff_mk_eq.mp g.property)
    exact h.trans ((classesEquiv e).apply_symm_apply c)

private theorem central_transport (d : PrincipalCongruenceBlockData G) (e : G ≃* K)
    (i : d.I) (c : ConjClasses K) :
    centralCharacterInCyclotomicOrder (d.transport e).eta_spec
      ((d.transport e).chi i) ((d.transport e).complete.1 i) c =
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) (d.complete.1 i)
      ((classesEquiv e).symm c) := by
  apply Subtype.ext
  change (Nat.card c.carrier : ℂ) * d.chi i ((classesEquiv e).symm c) /
    d.chi i (ConjClasses.mk (e.symm 1)) = _
  rw [map_one, class_card e c]
  rfl


@[simp] theorem transport_block (d : PrincipalCongruenceBlockData G) (e : G ≃* K) :
    (d.transport e).block = d.block := by
  ext i
  rw [mem_block_iff, mem_block_iff, sameTwoBlock_iff, sameTwoBlock_iff]
  simp only [central_transport d e i, central_transport d e d.principal]
  constructor
  · intro h c
    simpa only [Equiv.symm_apply_apply] using h ((classesEquiv e) c)
  · intro h c
    exact h ((classesEquiv e).symm c)

end PrincipalBlockConstruction.PrincipalCongruenceBlockData
namespace Cartan

/-- The localized selectors have identical corresponding coefficients. -/
theorem localizedSelector_transport_coeff (d : PrincipalCongruenceBlockData G)
    (e : G ≃* K) (k : K) :
    (localizedPrincipalBlockElement (d.transport e)).coeff k =
      (localizedPrincipalBlockElement d).coeff (e.symm k) := by
  apply localizationToComplex_injective d
  rw [← principalBlockElement_coeff_eq_localized (d.transport e) k,
    ← principalBlockElement_coeff_eq_localized d (e.symm k)]
  rw [principalBlockElement_coeff, principalBlockElement_coeff]
  rw [PrincipalCongruenceBlockData.transport_block, Nat.card_congr e.toEquiv]
  change (Nat.card K : ℂ)⁻¹ * ∑ i ∈ d.block,
    d.chi i (ConjClasses.mk (e.symm 1)) * d.chi i (ConjClasses.mk (e.symm k⁻¹)) = _
  rw [map_one, map_inv]

/-- The actual splitting-field selector is carried along the group isomorphism. -/
theorem splittingSelector_transport (d : PrincipalCongruenceBlockData G) (e : G ≃* K) :
    splittingSelector (d.transport e) =
      MonoidAlgebra.mapDomainRingEquiv (splittingField d) e (splittingSelector d) := by
  ext k
  simp only [MonoidAlgebra.coeff_mapDomainRingEquiv]
  change residueInclusion d (localizationToResidue d
    ((localizedPrincipalBlockElement (d.transport e)).coeff k)) =
      residueInclusion d (localizationToResidue d
        ((localizedPrincipalBlockElement d).coeff (e.symm k)))
  rw [localizedSelector_transport_coeff]

omit [Finite G] [Finite K] in
private theorem action_mapDomain {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (ρ : Representation F K V) (e : G ≃* K) (a : MonoidAlgebra F G) :
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainRingEquiv F e a) =
      Representation.asAlgebraHom (ρ.comp e.toMonoidHom) a := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simp [MonoidAlgebra.of, Representation.asAlgebraHom_single]
  | add a b ha hb => simp only [map_add, ha, hb]
  | smul r a ha =>
      simpa only [MonoidAlgebra.mapDomainRingEquiv, RingEquiv.ofRingHom_apply,
        MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul,
        map_smul] using congrArg (fun x => r • x) ha

/-- Block membership is preserved, with no selector compatibility hypothesis. -/
theorem inPrincipalBlock_transport_iff (d : PrincipalCongruenceBlockData G) (e : G ≃* K)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    (ρ : Representation (splittingField d) K V) :
    InPrincipalBlock (d.transport e) ρ ↔ InPrincipalBlock d (ρ.comp e.toMonoidHom) := by
  unfold InPrincipalBlock
  rw [splittingSelector_transport, action_mapDomain]

/-- Pullback retains the characteristic-zero lifted eigenvalue sum at the same prime. -/
theorem brauerValue_transport (d : PrincipalCongruenceBlockData G) (e : G ≃* K)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) K V) (g : G) (hg : Odd (orderOf g)) :
    BrauerCharacter.value (d.transport e) ρ (e g) =
      BrauerCharacter.value d (ρ.comp e.toMonoidHom) g := by
  apply congrArg (fun x : cyclotomicOrder d.eta => (x : ℂ))
  change ((ρ (e g)).charpoly.roots.map (BrauerCharacter.eigenvalueLift (d.transport e))).sum =
    ((ρ (e g)).charpoly.roots.map (BrauerCharacter.eigenvalueLift d)).sum
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  have hxpow := BrauerCharacter.eigenvalue_pow_orderOf d (ρ.comp e.toMonoidHom) g x hx
  have hdiv := orderOf_dvd_natCard g
  have hdiv' : orderOf g ∣ Nat.card K := (Nat.card_congr e.toEquiv) ▸ hdiv
  rw [BrauerCharacter.eigenvalueLift_eq_liftAtOrder (d.transport e) (orderOf g) hg hdiv' x hxpow,
    BrauerCharacter.eigenvalueLift_eq_liftAtOrder d (orderOf g) hg hdiv x hxpow]
  apply BrauerCharacter.odd_root_eq_of_reduction_eq d hg hg hdiv hdiv
    (BrauerCharacter.liftAtOrder_pow (d.transport e) _ _ _ _ _)
    (BrauerCharacter.liftAtOrder_pow d _ _ _ _ _)
  exact (BrauerCharacter.reduction_liftAtOrder (d.transport e) _ _ _ _ _).trans
    (BrauerCharacter.reduction_liftAtOrder d _ _ _ _ _).symm

omit [Finite G] [Finite K] in
private theorem comp_symm_equiv {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (e : G ≃* K) :
    (ρ.comp e.symm.toMonoidHom).comp e.toMonoidHom = ρ := by
  ext g
  simp

/-- Transport a complete independent family of actual simple block modules. -/
@[expose] def PrincipalBrauerFamily.transport {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (b : PrincipalBrauerFamily d n) (e : G ≃* K) : PrincipalBrauerFamily (d.transport e) n where
  degree := b.degree
  rep j := (b.rep j).comp e.symm.toMonoidHom
  irreducible j := (Representation.irreducible_comp_surjective_iff _ e.symm.surjective _).mpr
    (b.irreducible j)
  inBlock j := by
    rw [inPrincipalBlock_transport_iff]
    simpa only [comp_symm_equiv (b.rep j) e] using b.inBlock j
  complete m ρ hirr hblock := by
    obtain ⟨j, ⟨a⟩⟩ := b.complete m (ρ.comp e.toMonoidHom)
      ((Representation.irreducible_comp_surjective_iff _ e.surjective _).mpr hirr)
      ((inPrincipalBlock_transport_iff d e ρ).mp hblock)
    refine ⟨j, ⟨Representation.Equiv.mk a.toLinearEquiv ?_⟩⟩
    intro k
    simpa using a.isIntertwining' (e.symm k)
  independent := by
    rw [Fintype.linearIndependent_iff]
    intro coeff hcoeff
    apply Fintype.linearIndependent_iff.mp b.independent coeff
    funext c
    obtain ⟨g, hg, hc⟩ := c.property
    have hc' : c = BrauerCharacter.twoRegularClass g hg := Subtype.ext hc.symm
    rw [hc']
    have h := congrFun hcoeff (BrauerCharacter.twoRegularClass (e g)
      (by simpa only [e.orderOf_eq] using hg))
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      BrauerCharacter.character_apply, brauerValue_transport d e _ g hg,
      comp_symm_equiv _ e] using h

/-- Pull a family on the transported datum back to the original, prescribed datum. -/
@[expose] def PrincipalBrauerFamily.transportBack {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (e : G ≃* K) (b : PrincipalBrauerFamily (d.transport e) n) : PrincipalBrauerFamily d n where
  degree := b.degree
  rep j := (b.rep j).comp e.toMonoidHom
  irreducible j := (Representation.irreducible_comp_surjective_iff _ e.surjective _).mpr
    (b.irreducible j)
  inBlock j := (inPrincipalBlock_transport_iff d e _).mp (b.inBlock j)
  complete m ρ hirr hblock := by
    have hρ : InPrincipalBlock (d.transport e) (ρ.comp e.symm.toMonoidHom) := by
      rw [inPrincipalBlock_transport_iff]
      simpa only [comp_symm_equiv ρ e] using hblock
    obtain ⟨j, ⟨a⟩⟩ := b.complete m (ρ.comp e.symm.toMonoidHom)
      ((Representation.irreducible_comp_surjective_iff _ e.symm.surjective _).mpr hirr) hρ
    refine ⟨j, ⟨Representation.Equiv.mk a.toLinearEquiv ?_⟩⟩
    intro g
    simpa using a.isIntertwining' (e g)
  independent := by
    rw [Fintype.linearIndependent_iff]
    intro coeff hcoeff
    apply Fintype.linearIndependent_iff.mp b.independent coeff
    funext c
    obtain ⟨k, hk, hc⟩ := c.property
    have hc' : c = BrauerCharacter.twoRegularClass k hk := Subtype.ext hc.symm
    rw [hc']
    have hg : Odd (orderOf (e.symm k)) := by simpa only [e.symm.orderOf_eq] using hk
    have h := congrFun hcoeff (BrauerCharacter.twoRegularClass (e.symm k) hg)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      BrauerCharacter.character_apply] at h ⊢
    simpa only [← brauerValue_transport d e _ (e.symm k) hg,
      e.apply_symm_apply] using h

/-- Transport genuine decomposition numbers without reindexing rows or columns. -/
@[expose] def PrincipalDecompositionData.transport {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (a : PrincipalDecompositionData d n) (e : G ≃* K) :
    PrincipalDecompositionData (d.transport e) n where
  family := a.family.transport e
  decomposition := a.decomposition
  restriction i hi k hk := by
    have hg : Odd (orderOf (e.symm k)) := by simpa only [e.symm.orderOf_eq] using hk
    have h := a.restriction i (by simpa using hi) (e.symm k) hg
    change d.chi i (ConjClasses.mk (e.symm k)) = _
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hv := brauerValue_transport d e ((a.family.rep j).comp e.symm.toMonoidHom)
      (e.symm k) hg
    change BrauerCharacter.value d (a.family.rep j) (e.symm k) =
      BrauerCharacter.value (d.transport e) ((a.family.rep j).comp e.symm.toMonoidHom) k
    simpa only [e.apply_symm_apply, comp_symm_equiv _ e] using hv.symm


/-- Return decomposition data to the original datum, keeping its modular place. -/
@[expose] def PrincipalDecompositionData.transportBack {d : PrincipalCongruenceBlockData G}
    {n : ℕ} (e : G ≃* K) (a : PrincipalDecompositionData (d.transport e) n) :
    PrincipalDecompositionData d n where
  family := a.family.transportBack e
  decomposition := a.decomposition
  restriction i hi g hg := by
    have h := a.restriction i (by simpa using hi) (e g)
      (by simpa only [e.orderOf_eq] using hg)
    change d.chi i (ConjClasses.mk (e.symm (e g))) =
      ∑ j, (a.decomposition i j : ℂ) * BrauerCharacter.value (d.transport e)
        (a.family.rep j) (e g) at h
    change d.chi i (ConjClasses.mk g) =
      ∑ j, (a.decomposition i j : ℂ) * BrauerCharacter.value d
        ((a.family.rep j).comp e.toMonoidHom) g
    simpa only [e.symm_apply_apply, brauerValue_transport d e _ g hg] using h

@[simp] theorem PrincipalDecompositionData.transport_decomposition
    {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (a : PrincipalDecompositionData d n) (e : G ≃* K) (i : d.I) (j : Fin n) :
    (a.transport e).decomposition i j = a.decomposition i j := rfl

@[simp] theorem PrincipalDecompositionData.transportBack_decomposition
    {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (e : G ≃* K) (a : PrincipalDecompositionData (d.transport e) n) (i : d.I) (j : Fin n) :
    (a.transportBack e).decomposition i j = a.decomposition i j := rfl

@[simp] theorem PrincipalDecompositionData.transport_degree
    {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (a : PrincipalDecompositionData d n) (e : G ≃* K) (j : Fin n) :
    (a.transport e).family.degree j = a.family.degree j := rfl

@[simp] theorem PrincipalDecompositionData.transport_cartan
    {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (a : PrincipalDecompositionData d n) (e : G ≃* K) (j k : Fin n) :
    (a.transport e).cartan j k = a.cartan j k := by
  simp only [PrincipalDecompositionData.cartan, PrincipalDecompositionData.transport,
    PrincipalCongruenceBlockData.transport_block]

@[simp] theorem PrincipalDecompositionData.transportBack_degree
    {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (e : G ≃* K) (a : PrincipalDecompositionData (d.transport e) n) (j : Fin n) :
    (a.transportBack e).family.degree j = a.family.degree j := rfl

@[simp] theorem PrincipalDecompositionData.transportBack_cartan
    {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (e : G ≃* K) (a : PrincipalDecompositionData (d.transport e) n) (j k : Fin n) :
    (a.transportBack e).cartan j k = a.cartan j k := by
  simp only [PrincipalDecompositionData.cartan, PrincipalDecompositionData.transportBack,
    PrincipalCongruenceBlockData.transport_block]

end Cartan
end ModularBlock
