module

public import Theory.Character.ModularBlock.QuotientRepresentation
public import Theory.Character.ModularBlock.CartanKernel
public import Theory.Character.ModularBlock.CentralQuotientSelector
public import Theory.Character.ModularBlock.CentralQuotientOrdinaryKernel
public import Theory.Character.ModularBlock.PrincipalDecompositionExistence

/-!
# Central two-quotient principal families and Cartan comparison

Compatible inflation transports module isomorphisms. The quotient map sends
the ambient principal selector to the transported quotient selector, so it
preserves and reflects principal-block membership. Descent of every simple
module through a central two-subgroup proves completeness of the inflated
Brauer family, without changing its degrees.

The proved identity of ordinary block kernels forces Cartan scaling for genuine
decomposition data with matching Brauer values, by independence in both
variables. Constructing ambient decomposition data is reduced to realizing
ordinary block characters as genuine modular characters; composition factors
then supply nonnegative integral decomposition rows. Integral lattice reduction
provides these realizations, completing the unconditional transfer theorem.

These are assembly lemmas for the central quotient theorem
(cf. Feit, *The Representation Theory of Finite Groups*, III.2.13 and IV.4.12).
-/

public section

noncomputable section
open scoped BigOperators
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace ModularBlock.Cartan
open PrincipalBlockConstruction BrauerCoefficientExtension CompatibleLocalBlock
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A selector pushforward identity identifies block membership under compatible inflation. -/
theorem inflateQuotientRepresentation_inPrincipalBlock_iff_of_selector
    (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal]
    (hselector : MonoidAlgebra.mapDomainRingHom (splittingField d) (QuotientGroup.mk' N)
        (splittingSelector d) =
      MonoidAlgebra.mapRingHom (G ⧸ N) (quotientSplittingFieldEquiv d N : _ →+* _)
        (splittingSelector (compatibleQuotientPrincipalCongruenceBlockData d N)))
    {m : ℕ}
    (ρ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))) :
    InPrincipalBlock d (inflateQuotientRepresentation d N ρ) ↔
      InPrincipalBlock (compatibleQuotientPrincipalCongruenceBlockData d N) ρ := by
  unfold InPrincipalBlock inflateQuotientRepresentation
  rw [Representation.comp_asAlgebraHom_mapDomain, hselector,
    Representation.changeCoefficients_asAlgebraHom
      (quotientSplittingFieldEquiv d N) ρ]
  exact (Representation.coefficientEquiv (quotientSplittingFieldEquiv d N) m).conjRingEquiv.map_eq_one_iff

/-- Compatible inflation carries genuine module isomorphisms to ambient isomorphisms. -/
def inflateQuotientRepresentation_equiv (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] {m n : ℕ}
    {ρ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))}
    {σ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin n → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))}
    (e : ρ.Equiv σ) :
    (inflateQuotientRepresentation d N ρ).Equiv (inflateQuotientRepresentation d N σ) :=
  (Representation.inflationEquiv (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) _ _).symm
    (Representation.changeCoefficientsEquiv (quotientSplittingFieldEquiv d N) e)

/-- Inflate a complete principal Brauer family through a central two-subgroup,
once the actual selectors have been identified. -/
@[expose] def PrincipalBrauerFamily.centralTwoInflationOfSelector (d : PrincipalCongruenceBlockData G)
    (Z : Subgroup G) [Z.Normal] (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    (hselector : MonoidAlgebra.mapDomainRingHom (splittingField d) (QuotientGroup.mk' Z)
        (splittingSelector d) =
      MonoidAlgebra.mapRingHom (G ⧸ Z) (quotientSplittingFieldEquiv d Z : _ →+* _)
        (splittingSelector (compatibleQuotientPrincipalCongruenceBlockData d Z)))
    {n : ℕ} (b : PrincipalBrauerFamily (compatibleQuotientPrincipalCongruenceBlockData d Z) n) :
    PrincipalBrauerFamily d n where
  degree := b.degree
  rep j := inflateQuotientRepresentation d Z (b.rep j)
  irreducible j := (inflateQuotientRepresentation_irreducible_iff d Z (b.rep j)).mpr (b.irreducible j)
  inBlock j :=
    (inflateQuotientRepresentation_inPrincipalBlock_iff_of_selector d Z hselector (b.rep j)).mpr
      (b.inBlock j)
  complete m ρ hρ hblock := by
    let : Representation.IsIrreducible ρ := hρ
    obtain ⟨σ, hσ, heq⟩ := exists_centralTwo_compatible_descent d Z hcentral hZ ρ
    have hbσ : InPrincipalBlock (compatibleQuotientPrincipalCongruenceBlockData d Z) σ :=
      (inflateQuotientRepresentation_inPrincipalBlock_iff_of_selector d Z hselector σ).mp (heq ▸ hblock)
    obtain ⟨j, ⟨e⟩⟩ := b.complete m σ hσ hbσ
    refine ⟨j, ?_⟩
    rw [← heq]
    exact ⟨inflateQuotientRepresentation_equiv d Z e⟩
  independent := inflateQuotientRepresentation_independent d Z b.degree b.rep b.independent

/-- A quotient identity for ordinary block kernels determines the scaling of
all Cartan entries. This lemma requires genuine decomposition data on both sides;
it does not infer such data from the simple-module correspondence. -/
theorem PrincipalDecompositionData.cartan_eq_mul_of_quotient_ordinaryKernel {d : PrincipalCongruenceBlockData G} (N : Subgroup G) [N.Normal]
    {n : ℕ} (aG : PrincipalDecompositionData d n)
    (aQ : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d N) n)
    (c : ℕ)
    (hvalue : ∀ j g, Odd (orderOf g) →
      BrauerCharacter.value d (aG.family.rep j) g =
        BrauerCharacter.value (compatibleQuotientPrincipalCongruenceBlockData d N)
          (aQ.family.rep j) (QuotientGroup.mk' N g))
    (hkernel : ∀ g h : G, Odd (orderOf g) → Odd (orderOf h) →
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk g) * d.chi i (ConjClasses.mk h) =
        (c : ℂ) * ∑ i ∈ (compatibleQuotientPrincipalCongruenceBlockData d N).block,
          (compatibleQuotientPrincipalCongruenceBlockData d N).chi i
              (ConjClasses.mk (QuotientGroup.mk' N g)) *
            (compatibleQuotientPrincipalCongruenceBlockData d N).chi i
              (ConjClasses.mk (QuotientGroup.mk' N h))) :
    ∀ j k, aG.cartan j k = c * aQ.cartan j k := by
  have heq : aG.cartan = fun j k => c * aQ.cartan j k := by
    apply aG.cartan_eq_of_ordinaryKernel
    intro g h hg hh
    rw [hkernel g h hg hh, aQ.ordinaryKernel_eq _ _
      (hg.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' N) g))
      (hh.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' N) h))]
    simp_rw [hvalue _ g hg, hvalue _ h hh, Nat.cast_mul, Finset.mul_sum, mul_assoc]
  exact fun j k => congrFun (congrFun heq j) k

/-- Compatible inflation identifies actual principal-block modules across a
central two-subgroup quotient. -/
theorem inflateQuotientRepresentation_inPrincipalBlock_iff_of_centralTwo
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {m : ℕ}
    (ρ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d Z))
      (G ⧸ Z) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d Z))) :
    InPrincipalBlock d (inflateQuotientRepresentation d Z ρ) ↔
      InPrincipalBlock (compatibleQuotientPrincipalCongruenceBlockData d Z) ρ :=
  inflateQuotientRepresentation_inPrincipalBlock_iff_of_selector d Z
    (mapDomain_splittingSelector_eq_of_central_twoGroup d Z hcentral hZ) ρ

/-- The genuine complete principal Brauer family inflated through a central
two-subgroup, with exactly the same degrees. -/
@[expose] def PrincipalBrauerFamily.ofCentralTwoQuotient
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {n : ℕ}
    (b : PrincipalBrauerFamily (compatibleQuotientPrincipalCongruenceBlockData d Z) n) :
    PrincipalBrauerFamily d n :=
  b.centralTwoInflationOfSelector d Z hcentral hZ
    (mapDomain_splittingSelector_eq_of_central_twoGroup d Z hcentral hZ)

@[simp] theorem PrincipalBrauerFamily.ofCentralTwoQuotient_degree
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {n : ℕ}
    (b : PrincipalBrauerFamily (compatibleQuotientPrincipalCongruenceBlockData d Z) n) :
    (b.ofCentralTwoQuotient d Z hcentral hZ).degree = b.degree := rfl

/-- Inflation preserves the actual eigenvalue-defined Brauer values. -/
theorem PrincipalBrauerFamily.ofCentralTwoQuotient_value
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {n : ℕ}
    (b : PrincipalBrauerFamily (compatibleQuotientPrincipalCongruenceBlockData d Z) n)
    (j : Fin n) (g : G) (hg : Odd (orderOf g)) :
    BrauerCharacter.value d ((b.ofCentralTwoQuotient d Z hcentral hZ).rep j) g =
      BrauerCharacter.value (compatibleQuotientPrincipalCongruenceBlockData d Z)
        (b.rep j) (QuotientGroup.mk' Z g) :=
  inflateQuotientRepresentation_brauerValue d Z (b.rep j) g hg

/-- The ordinary kernel comparison proves central-two Cartan scaling whenever
genuine decomposition data have corresponding Brauer values. -/
theorem PrincipalDecompositionData.cartan_eq_mul_of_centralTwo_quotient
    {d : PrincipalCongruenceBlockData G} (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {n : ℕ}
    (aG : PrincipalDecompositionData d n)
    (aQ : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d Z) n)
    (hvalue : ∀ j g, Odd (orderOf g) →
      BrauerCharacter.value d (aG.family.rep j) g =
        BrauerCharacter.value (compatibleQuotientPrincipalCongruenceBlockData d Z)
          (aQ.family.rep j) (QuotientGroup.mk' Z g)) :
    ∀ j k, aG.cartan j k = Nat.card Z * aQ.cartan j k :=
  aG.cartan_eq_mul_of_quotient_ordinaryKernel Z aQ (Nat.card Z) hvalue
    (ordinaryKernel_centralTwo d Z hcentral hZ)

/-- Ordinary modular realizations suffice for constructing
genuine ambient decomposition data with the required degrees and Cartan matrix.
No decomposition rows or Cartan identities are assumed. -/
theorem exists_centralTwoQuotient_of_modular_realizations
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {n : ℕ}
    (aQ : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d Z) n)
    (hrealize : ∀ i ∈ d.block, ∃ (m : ℕ)
      (ρ : Representation (splittingField d) G (Fin m → splittingField d)),
      InPrincipalBlock d ρ ∧ ∀ g : G, Odd (orderOf g) →
        d.chi i (ConjClasses.mk g) = BrauerCharacter.value d ρ g) :
    ∃ aG : PrincipalDecompositionData d n,
      aG.family = aQ.family.ofCentralTwoQuotient d Z hcentral hZ ∧
      aG.family.degree = aQ.family.degree ∧
      ∀ j k, aG.cartan j k = Nat.card Z * aQ.cartan j k := by
  obtain ⟨aG, hfamily⟩ := exists_decompositionData_of_modular_realizations
    (aQ.family.ofCentralTwoQuotient d Z hcentral hZ) hrealize
  refine ⟨aG, hfamily, ?_, ?_⟩
  · rw [hfamily]
    rfl
  · apply aG.cartan_eq_mul_of_centralTwo_quotient Z hcentral hZ aQ
    intro j g hg
    rw [hfamily]
    exact aQ.family.ofCentralTwoQuotient_value d Z hcentral hZ j g hg

/-- A central two-subgroup quotient admits genuine ambient principal decomposition
data with the inflated family, unchanged degrees, and Cartan matrix multiplied
by the order of the central subgroup. -/
theorem exists_centralTwoQuotient
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {n : ℕ}
    (aQ : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d Z) n) :
    ∃ aG : PrincipalDecompositionData d n,
      aG.family = aQ.family.ofCentralTwoQuotient d Z hcentral hZ ∧
      aG.family.degree = aQ.family.degree ∧
      ∀ j k, aG.cartan j k = Nat.card Z * aQ.cartan j k :=
  exists_centralTwoQuotient_of_modular_realizations d Z hcentral hZ aQ
    (exists_modular_realization d)

end ModularBlock.Cartan
