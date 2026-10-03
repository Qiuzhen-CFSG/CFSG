module

public import Theory.Character.ModularBlock.Cartan
public import Theory.Character.ModularBlock.BrauerQuotientExtension
public import Theory.Representation.CoefficientTransport
public import Theory.Character.ModularBlock.PrincipalKernel
public import Theory.Representation.Quotient
public import Theory.GroupTheory.PRegularLift

/-!
# Compatible representation inflation and quotient descent

Ordinary irreducibles in the actual principal congruence block kill every
odd normal subgroup, by the odd-core kernel theorem. They therefore descend
as irreducible quotient representations of the same degree. At the actual
ambient modular place, central two-subgroups kill every simple module;
each representation of a principal Brauer family descends with the same
degree. The compatible splitting-field equivalence transports the quotient's
actual matrices to the ambient field. Its commutative reduction square and
the characteristic-polynomial formula prove equality of genuine Brauer values
under inflation. Every odd-order quotient element has an odd-order preimage,
so linear independence of Brauer characters is preserved as well.
Irreducibility is preserved, and every simple module of a central two-extension
is recovered by this compatible inflation.

These are representation-level ingredients for the odd-normal and central-two
Cartan comparisons (Feit, *The Representation Theory of Finite Groups*,
III.2.13 and IV.4.12). They do not assert a Cartan formula. Identification with
the quotient's principal block and comparison of decomposition multiplicities
remain separate steps. All coefficient comparisons use the canonical datum
`compatibleQuotientPrincipalCongruenceBlockData`, retaining the prescribed
root and contracted prime. The statements here supply the common representation
layer for the two different Cartan transfer arguments.
-/

public section
noncomputable section
namespace ModularBlock.Cartan

open PrincipalBlockConstruction BrauerCoefficientExtension CompatibleLocalBlock

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every ordinary irreducible in the principal block kills any odd normal subgroup. -/
theorem oddNormal_le_ordinary_ker (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    {i : d.I} (hi : i ∈ d.block) {m : ℕ}
    (ρ : Representation ℂ G (Fin m → ℂ))
    (hρ : d.chi i = characterClassFunction ρ) : N ≤ ρ.ker := by
  have hcore : N ≤ pPrimeCore 2 G :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hN⟩
  exact hcore.trans
    (PrincipalBlockKernel.pPrimeCore_le_representation_ker_of_mem_block d hi ρ hρ)

/-- Ordinary principal-block characters descend as genuine irreducible
representations, on the same standard complex vector space. -/
theorem exists_oddNormal_ordinary_descent (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (i : d.I) (hi : i ∈ d.block) :
    ∃ (m : ℕ) (σ : Representation ℂ (G ⧸ N) (Fin m → ℂ)),
      Representation.IsIrreducible σ ∧
      d.chi i = characterClassFunction (σ.comp (QuotientGroup.mk' N)) := by
  obtain ⟨m, ρ, hρ⟩ := (d.complete.1 i).1
  have hker := oddNormal_le_ordinary_ker d N hN hi ρ hρ
  refine ⟨m, Representation.quotientOfLEKer ρ N hker, ?_, hρ⟩
  apply (Representation.quotientOfLEKer_irreducible_iff ρ N hker).mpr
  apply (irreducible_iff_character_norm_one (ρ := ρ)).mpr
  rw [← hρ]
  exact (d.complete.1 i).2

/-- At the prescribed ambient modular place, every simple representation
kills a central two-subgroup. No block hypothesis is necessary. -/
theorem centralTwo_le_modular_ker (d : PrincipalCongruenceBlockData G)
    (Z : Subgroup G) (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) [Representation.IsIrreducible ρ] :
    Z ≤ ρ.ker :=
  Representation.central_pSubgroup_le_ker 2 ρ Z hcentral hZ

/-- The descended simple module uses exactly the same vector space and
ambient coefficient field. Comparing with the quotient's prescribed splitting
field is a separate coefficient-transport step. -/
@[expose] def centralTwoQuotientRepresentation (d : PrincipalCongruenceBlockData G)
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) [Representation.IsIrreducible ρ] :
    Representation (splittingField d) (G ⧸ Z) V :=
  Representation.quotientOfLEKer ρ Z (centralTwo_le_modular_ker d Z hcentral hZ ρ)

@[simp] theorem centralTwoQuotientRepresentation_comp (d : PrincipalCongruenceBlockData G)
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) [Representation.IsIrreducible ρ] :
    (centralTwoQuotientRepresentation d Z hcentral hZ ρ).comp (QuotientGroup.mk' Z) = ρ := rfl

theorem centralTwoQuotientRepresentation_irreducible (d : PrincipalCongruenceBlockData G)
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (centralTwoQuotientRepresentation d Z hcentral hZ ρ) :=
  (Representation.quotientOfLEKer_irreducible_iff ρ Z _).mpr inferInstance

/-- Each column of a genuine principal Brauer family descends through a
central two-subgroup, retaining its exact degree. -/
theorem PrincipalBrauerFamily.exists_centralTwo_descent
    {d : PrincipalCongruenceBlockData G} {n : ℕ} (b : PrincipalBrauerFamily d n)
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) :
    ∃ σ : (j : Fin n) → Representation (splittingField d) (G ⧸ Z)
        (Fin (b.degree j) → splittingField d),
      (∀ j, Representation.IsIrreducible (σ j)) ∧
      ∀ j, (σ j).comp (QuotientGroup.mk' Z) = b.rep j := by
  let (j : Fin n) : Representation.IsIrreducible (b.rep j) := b.irreducible j
  exact ⟨fun j => centralTwoQuotientRepresentation d Z hcentral hZ (b.rep j),
    fun j => centralTwoQuotientRepresentation_irreducible d Z hcentral hZ (b.rep j),
    fun j => centralTwoQuotientRepresentation_comp d Z hcentral hZ (b.rep j)⟩

/-- Brauer eigenvalue sums at the prescribed place are constant on cosets
of a subgroup acting trivially. This compares actual matrices, not traces
reduced modulo two. -/
theorem brauerValue_eq_of_quotient_eq (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal]
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) (hN : N ≤ ρ.ker)
    {g h : G} (hgh : QuotientGroup.mk' N g = QuotientGroup.mk' N h) :
    BrauerCharacter.value d ρ g = BrauerCharacter.value d ρ h := by
  have hmatrix : ρ g = ρ h :=
    congrArg (Representation.quotientOfLEKer ρ N hN) hgh
  simp only [BrauerCharacter.value, BrauerCharacter.integralValue, hmatrix]

theorem centralTwo_brauerValue_eq_of_quotient_eq (d : PrincipalCongruenceBlockData G)
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) [Representation.IsIrreducible ρ]
    {g h : G} (hgh : QuotientGroup.mk' Z g = QuotientGroup.mk' Z h) :
    BrauerCharacter.value d ρ g = BrauerCharacter.value d ρ h :=
  brauerValue_eq_of_quotient_eq d Z ρ (centralTwo_le_modular_ker d Z hcentral hZ ρ) hgh

/-- Inflate a quotient representation at the prescribed modular place,
transporting its matrices along the compatible splitting-field equivalence. -/
@[expose] def inflateQuotientRepresentation (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] {m : ℕ}
    (ρ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))) :
    Representation (splittingField d) G (Fin m → splittingField d) :=
  (Representation.changeCoefficients (quotientSplittingFieldEquiv d N) ρ).comp
    (QuotientGroup.mk' N)

theorem inflateQuotientRepresentation_irreducible_iff (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] {m : ℕ}
    (ρ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))) :
    Representation.IsIrreducible (inflateQuotientRepresentation d N ρ) ↔
      Representation.IsIrreducible ρ := by
  rw [inflateQuotientRepresentation, Representation.irreducible_comp_surjective_iff
    _ (QuotientGroup.mk'_surjective N), Representation.changeCoefficients_irreducible_iff]

/-- Genuine Brauer characters inflate with their characteristic-zero
multiplicities, not just their reductions modulo two. -/
theorem inflateQuotientRepresentation_brauerValue (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] {m : ℕ}
    (ρ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N)))
    (g : G) (hg : Odd (orderOf g)) :
    BrauerCharacter.value d (inflateQuotientRepresentation d N ρ) g =
      BrauerCharacter.value (compatibleQuotientPrincipalCongruenceBlockData d N) ρ
        (QuotientGroup.mk' N g) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  let inclusion : cyclotomicOrder q.eta →+* cyclotomicOrder d.eta :=
    cyclotomicOrderInclusion (quotientRoot_mem d N)
  have hgq : Odd (orderOf (QuotientGroup.mk' N g)) :=
    hg.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' N) g)
  have hsum : BrauerCharacter.integralValue d (inflateQuotientRepresentation d N ρ) g =
      inclusion (BrauerCharacter.integralValue q ρ (QuotientGroup.mk' N g)) := by
    change (((Representation.changeCoefficients (quotientSplittingFieldEquiv d N) ρ)
        (QuotientGroup.mk' N g)).charpoly.roots.map (BrauerCharacter.eigenvalueLift d)).sum =
      inclusion (((ρ (QuotientGroup.mk' N g)).charpoly.roots.map
        (BrauerCharacter.eigenvalueLift q)).sum)
    rw [Representation.changeCoefficients_charpoly, (IsAlgClosed.splits _).roots_map,
      Multiset.map_map, map_multiset_sum, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    exact BrauerCharacter.eigenvalueLift_quotientSplittingFieldEquiv d N x
      (BrauerCharacter.eigenvalue_isLiftable q ρ (QuotientGroup.mk' N g) hgq x hx)
  exact congrArg (fun x : cyclotomicOrder d.eta => (x : ℂ)) hsum

/-- Simple modules descend to the quotient's actual prescribed splitting
field, and compatible inflation recovers the original matrices exactly. -/
theorem exists_centralTwo_compatible_descent (d : PrincipalCongruenceBlockData G)
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) {m : ℕ}
    (ρ : Representation (splittingField d) G (Fin m → splittingField d))
    [Representation.IsIrreducible ρ] :
    ∃ σ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d Z))
        (G ⧸ Z) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d Z)),
      Representation.IsIrreducible σ ∧ inflateQuotientRepresentation d Z σ = ρ := by
  let τ := centralTwoQuotientRepresentation d Z hcentral hZ ρ
  let e := quotientSplittingFieldEquiv d Z
  refine ⟨Representation.changeCoefficients e.symm τ, ?_, ?_⟩
  · apply (Representation.changeCoefficients_irreducible_iff _ _).mpr
    exact centralTwoQuotientRepresentation_irreducible d Z hcentral hZ ρ
  · change (Representation.changeCoefficients e
        (Representation.changeCoefficients e.symm τ)).comp (QuotientGroup.mk' Z) = ρ
    have he : Representation.changeCoefficients e
        (Representation.changeCoefficients e.symm τ) = τ := by
      simpa only [RingEquiv.symm_symm] using
        Representation.changeCoefficients_symm e.symm τ
    rw [he]
    exact centralTwoQuotientRepresentation_comp d Z hcentral hZ ρ

/-- Compatible inflation preserves independence of genuine Brauer characters. -/
theorem inflateQuotientRepresentation_independent (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] {n : ℕ} (degree : Fin n → ℕ)
    (ρ : (j : Fin n) →
      Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
        (G ⧸ N) (Fin (degree j) →
          splittingField (compatibleQuotientPrincipalCongruenceBlockData d N)))
    (hind : LinearIndependent ℂ (fun j =>
      BrauerCharacter.character (compatibleQuotientPrincipalCongruenceBlockData d N) (ρ j))) :
    LinearIndependent ℂ (fun j =>
      BrauerCharacter.character d (inflateQuotientRepresentation d N (ρ j))) := by
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro coeff hcoeff
  apply hind coeff
  funext c
  obtain ⟨q, hq, hc⟩ := c.property
  obtain ⟨g, hg, hquot⟩ := (QuotientGroup.mk' N).exists_pRegular_lift
    (QuotientGroup.mk'_surjective N) 2 Nat.prime_two q
    (by simpa only [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hq))
  have hgodd : Odd (orderOf g) := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hg)
  have hclass : c = BrauerCharacter.twoRegularClass q hq := Subtype.ext hc.symm
  have heq := congrFun hcoeff (BrauerCharacter.twoRegularClass g hgodd)
  rw [hclass]
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, BrauerCharacter.character_apply,
    inflateQuotientRepresentation_brauerValue d N _ g hgodd, hquot] using heq

end ModularBlock.Cartan
