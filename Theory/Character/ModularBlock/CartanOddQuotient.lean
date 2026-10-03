module

public import Theory.Character.ModularBlock.QuotientRepresentation
public import Theory.Character.ModularBlock.OrdinaryOddQuotient

/-!
# Principal-block descent through an odd normal subgroup

The ordinary odd-core kernel theorem makes the complex principal selector
invariant under multiplication by an odd normal subgroup. Injectivity of the
localized coefficient embedding, followed by reduction, gives the same
invariance for the actual modular selector. Consequently every representation
on which that selector acts identically kills the odd normal subgroup.
Compatible coefficient transport gives descent over the quotient's prescribed
splitting field, with unchanged dimension and genuine Brauer values.

The ordinary block equivalence from `OrdinaryOddQuotient` identifies the
complex selectors: summing their coefficients over a quotient fiber cancels
the kernel order against the group-order normalization. Injective localization
and compatible reduction identify the actual splitting-field selectors.
Consequently compatible inflation identifies principal-block modules. It
inflates a complete Brauer family and transports the actual decomposition
rows; reindexing their Gram matrix preserves every Cartan entry. The final
`PrincipalDecompositionData.ofOddQuotient` requires no correspondence or
multiplicity hypotheses.

These are ingredients for the odd-normal Cartan comparison (Feit,
*The Representation Theory of Finite Groups*, III.2.13 and IV.4.12).
-/

public section
noncomputable section
namespace ModularBlock.Cartan

open PrincipalBlockConstruction BrauerCoefficientExtension CompatibleLocalBlock
open BlockOrthogonality BrauerBlockReduction

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Odd normal elements fix the actual principal selector over the splitting field. -/
theorem single_mul_splittingSelector_of_mem_oddNormal
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {v : G} (hv : v ∈ N) :
    MonoidAlgebra.single v 1 * splittingSelector d = splittingSelector d := by
  have hcore : N ≤ pPrimeCore 2 G :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hN⟩
  have hcomplex : MonoidAlgebra.single v 1 * principalBlockElement d =
      principalBlockElement d := by
    ext g
    simp only [MonoidAlgebra.coeff_single_mul_apply, one_mul,
      principalBlockElement_coeff, mul_inv_rev, inv_inv]
    rw [PrincipalBlockKernel.weighted_block_sum_mul_right_eq d
      (fun i => d.chi i (ConjClasses.mk 1)) g⁻¹ v (hcore hv)]
  have hlocal : MonoidAlgebra.single v 1 * localizedPrincipalBlockElement d =
      localizedPrincipalBlockElement d := by
    ext g
    apply localizationToComplex_injective d
    simpa only [MonoidAlgebra.coeff_single_mul_apply, one_mul,
      ← principalBlockElement_coeff_eq_localized] using
      congrArg (fun x : MonoidAlgebra ℂ G => x.coeff g) hcomplex
  have hresidue := congrArg (reduceLocalizedGroupAlgebra d) hlocal
  have hsplit := congrArg (MonoidAlgebra.mapRingHom G (residueInclusion d)) hresidue
  simpa only [map_mul, splittingSelector, reducedPrincipalBlockElement,
    reduceLocalizedGroupAlgebra, MonoidAlgebra.mapRingHom_single, map_one] using hsplit

/-- Every module in the actual principal block kills an odd normal subgroup;
neither simplicity nor finite dimensionality is needed. -/
theorem oddNormal_le_modular_ker (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    (ρ : Representation (splittingField d) G V) (hblock : InPrincipalBlock d ρ) :
    N ≤ ρ.ker := by
  intro v hv
  have h := congrArg ρ.asAlgebraHom
    (single_mul_splittingSelector_of_mem_oddNormal d N hN hv)
  change ρ.asAlgebraHom (splittingSelector d) = 1 at hblock
  simpa only [map_mul, Representation.asAlgebraHom_single_one, hblock, mul_one,
    MonoidHom.mem_ker] using h

/-- Descent of a genuine principal-block simple representation to the quotient's
prescribed splitting field. Compatible inflation recovers the matrices exactly. -/
theorem exists_oddNormal_compatible_descent (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) {m : ℕ}
    (ρ : Representation (splittingField d) G (Fin m → splittingField d))
    (hρ : Representation.IsIrreducible ρ) (hblock : InPrincipalBlock d ρ) :
    ∃ σ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
        (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N)),
      Representation.IsIrreducible σ ∧ inflateQuotientRepresentation d N σ = ρ := by
  let τ := Representation.quotientOfLEKer ρ N (oddNormal_le_modular_ker d N hN ρ hblock)
  let e := quotientSplittingFieldEquiv d N
  refine ⟨Representation.changeCoefficients e.symm τ, ?_, ?_⟩
  · apply (Representation.changeCoefficients_irreducible_iff _ _).mpr
    exact (Representation.quotientOfLEKer_irreducible_iff ρ N _).mpr hρ
  · change (Representation.changeCoefficients e
        (Representation.changeCoefficients e.symm τ)).comp (QuotientGroup.mk' N) = ρ
    have he : Representation.changeCoefficients e
        (Representation.changeCoefficients e.symm τ) = τ := by
      simpa only [RingEquiv.symm_symm] using
        Representation.changeCoefficients_symm e.symm τ
    rw [he]
    rfl

/-- Inflate a complete principal Brauer family after identifying the actual blocks.
The block correspondence remains an explicit prerequisite of this construction. -/
@[expose] def PrincipalBrauerFamily.ofOddQuotientBlockCorrespondence (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) {n : ℕ}
    (b : PrincipalBrauerFamily (compatibleQuotientPrincipalCongruenceBlockData d N) n)
    (hblock : ∀ {m : ℕ} (ρ : Representation
      (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))),
      InPrincipalBlock d (inflateQuotientRepresentation d N ρ) ↔
      InPrincipalBlock (compatibleQuotientPrincipalCongruenceBlockData d N) ρ) :
    PrincipalBrauerFamily d n where
  degree := b.degree
  rep j := inflateQuotientRepresentation d N (b.rep j)
  irreducible j := (inflateQuotientRepresentation_irreducible_iff d N _).mpr (b.irreducible j)
  inBlock j := (hblock _).mpr (b.inBlock j)
  independent := inflateQuotientRepresentation_independent d N b.degree b.rep b.independent
  complete m ρ hρ hρblock := by
    obtain ⟨σ, hσ, heq⟩ := exists_oddNormal_compatible_descent d N hN ρ hρ hρblock
    obtain ⟨j, ⟨e⟩⟩ := b.complete m σ hσ ((hblock σ).mp (heq.symm ▸ hρblock))
    refine ⟨j, ⟨?_⟩⟩
    rw [← heq]
    exact (Representation.inflationEquiv (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) _ _).symm
        (Representation.changeCoefficientsEquiv (quotientSplittingFieldEquiv d N) e)

open scoped BigOperators

/-- Transfer the actual decomposition rows along a character correspondence.
No decomposition multiplicities or Cartan identities are supplied as hypotheses. -/
@[expose] def PrincipalDecompositionData.ofQuotientCorrespondence (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] {n : ℕ}
    (a : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d N) n)
    (b : PrincipalBrauerFamily d n)
    (e : {i // i ∈ d.block} ≃
      {i // i ∈ (compatibleQuotientPrincipalCongruenceBlockData d N).block})
    (hchi : ∀ i g, d.chi i.val (ConjClasses.mk g) =
      (compatibleQuotientPrincipalCongruenceBlockData d N).chi (e i).val
        (ConjClasses.mk (QuotientGroup.mk' N g)))
    (hvalue : ∀ j g, Odd (orderOf g) →
      BrauerCharacter.value d (b.rep j) g =
      BrauerCharacter.value (compatibleQuotientPrincipalCongruenceBlockData d N)
        (a.family.rep j) (QuotientGroup.mk' N g)) : PrincipalDecompositionData d n where
  family := b
  decomposition i j := if hi : i ∈ d.block then a.decomposition (e ⟨i, hi⟩).val j else 0
  restriction i hi g hg := by
    rw [hchi ⟨i, hi⟩ g, a.restriction (e ⟨i, hi⟩).val (e ⟨i, hi⟩).property
      _ (hg.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' N) g))]
    simp only [dif_pos hi, hvalue _ _ hg]

/-- A bijection of ordinary block rows preserves their decomposition Gram matrix. -/
theorem PrincipalDecompositionData.ofQuotientCorrespondence_cartan (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] {n : ℕ}
    (a : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d N) n)
    (b : PrincipalBrauerFamily d n)
    (e : {i // i ∈ d.block} ≃
      {i // i ∈ (compatibleQuotientPrincipalCongruenceBlockData d N).block})
    (hchi : ∀ i g, d.chi i.val (ConjClasses.mk g) =
      (compatibleQuotientPrincipalCongruenceBlockData d N).chi (e i).val
        (ConjClasses.mk (QuotientGroup.mk' N g)))
    (hvalue : ∀ j g, Odd (orderOf g) →
      BrauerCharacter.value d (b.rep j) g =
      BrauerCharacter.value (compatibleQuotientPrincipalCongruenceBlockData d N)
        (a.family.rep j) (QuotientGroup.mk' N g)) (j k : Fin n) :
    (PrincipalDecompositionData.ofQuotientCorrespondence d N a b e hchi hvalue).cartan j k = a.cartan j k := by
  classical
  simp only [PrincipalDecompositionData.cartan, PrincipalDecompositionData.ofQuotientCorrespondence]
  trans ∑ i : {i // i ∈ d.block}, a.decomposition (e i).val j * a.decomposition (e i).val k
  · rw [Finset.sum_subtype d.block]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [dif_pos i.property]
    · intro x; rfl
  · rw [Fintype.sum_equiv e _ (fun i => a.decomposition i.val j * a.decomposition i.val k)
      (fun _ => rfl)]
    exact (Finset.sum_subtype
      (compatibleQuotientPrincipalCongruenceBlockData d N).block (fun _ => Iff.rfl)
      (fun i => a.decomposition i j * a.decomposition i k)).symm

attribute [local instance] Fintype.ofFinite Classical.propDecidable
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
private theorem mapDomain_coeff {R H : Type*} [CommRing R] [Group H]
    (f : G →* H) (a : MonoidAlgebra R G) (y : H) :
    (MonoidAlgebra.mapDomainRingHom R f a).coeff y =
      ∑ g : G, if f g = y then a.coeff g else 0 := by
  classical
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain,
    Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
  exact Finsupp.sum_fintype _ _ (fun _ => by simp)

private theorem mapDomain_coeff_of_constant {R H : Type*} [CommRing R] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (a : MonoidAlgebra R G) (y : H) (c : R)
    (hc : ∀ g, f g = y → a.coeff g = c) :
    (MonoidAlgebra.mapDomainRingHom R f a).coeff y = (Nat.card f.ker : R) * c := by
  classical
  rw [mapDomain_coeff]
  calc
    _ = ∑ g : G, if f g = y then c else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      split_ifs with hg
      · exact hc g hg
      · rfl
    _ = (Nat.card {g : G // f g = y} : R) * c := by
      simp [← Finset.sum_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := by
      rw [show Nat.card {g : G // f g = y} = Nat.card f.ker from
        Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf y)]

/-- The complex principal selector maps to the quotient principal selector. -/
theorem mapDomain_principalBlockElement_eq_of_oddNormal (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) :
    MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' N) (principalBlockElement d) =
      principalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d N) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  let e := OrdinaryOddQuotient.blockEquiv d N hN
  have hsum (g : G) :
      (∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk g⁻¹)) =
      ∑ j ∈ q.block, q.chi j (ConjClasses.mk 1) *
        q.chi j (ConjClasses.mk ((QuotientGroup.mk' N g)⁻¹)) := by
    rw [Finset.sum_subtype d.block (fun _ => Iff.rfl),
      Finset.sum_subtype q.block (fun _ => Iff.rfl)]
    apply Fintype.sum_equiv e
    intro i
    rw [OrdinaryOddQuotient.blockEquiv_character d N hN i 1,
      OrdinaryOddQuotient.blockEquiv_character d N hN i g⁻¹]
    simp only [map_one, map_inv]
    rfl
  ext y
  rw [mapDomain_coeff_of_constant (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) _ y
    ((Nat.card G : ℂ)⁻¹ * ∑ j ∈ q.block,
      q.chi j (ConjClasses.mk 1) * q.chi j (ConjClasses.mk y⁻¹))
    (fun g hg => by rw [principalBlockElement_coeff, hsum, hg])]
  rw [QuotientGroup.ker_mk', principalBlockElement_coeff,
    Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.cast_mul]
  have hn : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  have hq : (Nat.card (G ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  field_simp
  rfl

private theorem quotientLocalization_complex (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] :
    (localizationToComplex d.primeIdeal).comp
        (compatibleQuotientLocalizationInclusion d N) =
      localizationToComplex
        (compatibleQuotientPrincipalCongruenceBlockData d N).primeIdeal := by
  apply IsLocalization.ringHom_ext
    (compatibleQuotientPrincipalCongruenceBlockData d N).primeIdeal.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [compatibleQuotientLocalizationInclusion_algebraMap,
    localizationToComplex_algebraMap,
    localizationToComplex_algebraMap]
  exact Subring.coe_inclusion _ a

private theorem quotientLocalization_residue (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] :
    (localizationToResidue d).comp (compatibleQuotientLocalizationInclusion d N) =
      (compatibleQuotientResidueFieldInclusion d N).comp
        (localizationToResidue (compatibleQuotientPrincipalCongruenceBlockData d N)) := by
  apply IsLocalization.ringHom_ext
    (compatibleQuotientPrincipalCongruenceBlockData d N).primeIdeal.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [compatibleQuotientLocalizationInclusion_algebraMap,
    localizationToResidue_algebraMap, localizationToResidue_algebraMap]
  exact (compatibleQuotientResidueFieldInclusion_mk d N a).symm

/-- The actual localized principal selectors agree under quotient and inclusion. -/
theorem mapDomain_localizedPrincipalBlockElement_eq_of_oddNormal
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) :
    MonoidAlgebra.mapDomainRingHom (Localization.AtPrime d.primeIdeal)
        (QuotientGroup.mk' N) (localizedPrincipalBlockElement d) =
      MonoidAlgebra.mapRingHom (G ⧸ N) (compatibleQuotientLocalizationInclusion d N)
        (localizedPrincipalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d N)) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  have hd := mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement d
    (localizationToComplex d.primeIdeal)
    (localizationToComplex_algebraMap d.primeIdeal)
  have hs := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
      (localizationToComplex d.primeIdeal) (QuotientGroup.mk' N))
    (localizedPrincipalBlockElement d)
  change MonoidAlgebra.mapRingHom (G ⧸ N) (localizationToComplex d.primeIdeal)
      (MonoidAlgebra.mapDomainRingHom (Localization.AtPrime d.primeIdeal)
        (QuotientGroup.mk' N) (localizedPrincipalBlockElement d)) =
    MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' N)
      (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
        (localizedPrincipalBlockElement d)) at hs
  rw [hd, mapDomain_principalBlockElement_eq_of_oddNormal d N hN] at hs
  ext x
  apply localizationToComplex_injective d
  have hx := congrArg (fun a : MonoidAlgebra ℂ (G ⧸ N) => a.coeff x) hs
  simp only [MonoidAlgebra.coeff_mapRingHom] at hx ⊢
  rw [hx, principalBlockElement_coeff_eq_localized]
  exact (RingHom.congr_fun (quotientLocalization_complex d N)
    ((localizedPrincipalBlockElement q).coeff x)).symm

/-- Reduction preserves the selector identity at the contracted prime. -/
theorem mapDomain_reducedPrincipalBlockElement_eq_of_oddNormal
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) :
    MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' N)
        (reducedPrincipalBlockElement d) =
      MonoidAlgebra.mapRingHom (G ⧸ N) (compatibleQuotientResidueFieldInclusion d N)
        (reducedPrincipalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d N)) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  have hs := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
      (localizationToResidue d) (QuotientGroup.mk' N)) (localizedPrincipalBlockElement d)
  change MonoidAlgebra.mapRingHom (G ⧸ N) (localizationToResidue d)
      (MonoidAlgebra.mapDomainRingHom (Localization.AtPrime d.primeIdeal)
        (QuotientGroup.mk' N) (localizedPrincipalBlockElement d)) =
    MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' N)
      (reducedPrincipalBlockElement d) at hs
  rw [← hs, mapDomain_localizedPrincipalBlockElement_eq_of_oddNormal d N hN]
  ext x
  simp only [reducedPrincipalBlockElement, reduceLocalizedGroupAlgebra,
    MonoidAlgebra.coeff_mapRingHom]
  exact RingHom.congr_fun (quotientLocalization_residue d N)
    ((localizedPrincipalBlockElement q).coeff x)

/-- The prescribed splitting-field equivalence identifies the principal selectors. -/
theorem mapDomain_splittingSelector_eq_of_oddNormal
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) :
    MonoidAlgebra.mapDomainRingHom (splittingField d) (QuotientGroup.mk' N)
        (splittingSelector d) =
      MonoidAlgebra.mapRingHom (G ⧸ N) (quotientSplittingFieldEquiv d N : _ →+* _)
        (splittingSelector (compatibleQuotientPrincipalCongruenceBlockData d N)) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  have hsquare : (residueInclusion d).comp (compatibleQuotientResidueFieldInclusion d N) =
      (quotientSplittingFieldEquiv d N : _ →+* _).comp (residueInclusion q) := by
    ext x
    exact (quotientSplittingFieldEquiv_residueInclusion d N x).symm
  have hcomm := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
      (residueInclusion d) (QuotientGroup.mk' N)) (reducedPrincipalBlockElement d)
  change MonoidAlgebra.mapRingHom (G ⧸ N) (residueInclusion d)
      (MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' N)
        (reducedPrincipalBlockElement d)) =
    MonoidAlgebra.mapDomainRingHom (splittingField d) (QuotientGroup.mk' N)
      (splittingSelector d) at hcomm
  rw [← hcomm, mapDomain_reducedPrincipalBlockElement_eq_of_oddNormal d N hN]
  change (MonoidAlgebra.mapRingHom (G ⧸ N) (residueInclusion d)).comp
      (MonoidAlgebra.mapRingHom (G ⧸ N) (compatibleQuotientResidueFieldInclusion d N))
      (reducedPrincipalBlockElement q) =
    (MonoidAlgebra.mapRingHom (G ⧸ N) (quotientSplittingFieldEquiv d N : _ →+* _)).comp
      (MonoidAlgebra.mapRingHom (G ⧸ N) (residueInclusion q))
      (reducedPrincipalBlockElement q)
  rw [← MonoidAlgebra.mapRingHom_comp, ← MonoidAlgebra.mapRingHom_comp, hsquare]

/-- Compatible inflation identifies actual principal-block modules. -/
theorem inflateQuotientRepresentation_inPrincipalBlock_iff_of_oddNormal
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {m : ℕ}
    (ρ : Representation (splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
      (G ⧸ N) (Fin m → splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))) :
    InPrincipalBlock d (inflateQuotientRepresentation d N ρ) ↔
      InPrincipalBlock (compatibleQuotientPrincipalCongruenceBlockData d N) ρ := by
  unfold InPrincipalBlock inflateQuotientRepresentation
  rw [Representation.comp_asAlgebraHom_mapDomain,
    mapDomain_splittingSelector_eq_of_oddNormal d N hN,
    Representation.changeCoefficients_asAlgebraHom]
  exact (Representation.coefficientEquiv (quotientSplittingFieldEquiv d N) m).conjRingEquiv.map_eq_one_iff

/-- Inflate the genuine complete principal Brauer family through an odd normal subgroup. -/
@[expose] def PrincipalBrauerFamily.ofOddQuotient
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {n : ℕ}
    (b : PrincipalBrauerFamily (compatibleQuotientPrincipalCongruenceBlockData d N) n) :
    PrincipalBrauerFamily d n :=
  .ofOddQuotientBlockCorrespondence d N hN b
    (inflateQuotientRepresentation_inPrincipalBlock_iff_of_oddNormal d N hN)

/-- The principal decomposition data of the quotient give genuine data upstairs. -/
@[expose] def PrincipalDecompositionData.ofOddQuotient
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {n : ℕ}
    (a : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d N) n) :
    PrincipalDecompositionData d n :=
  .ofQuotientCorrespondence d N a
    (.ofOddQuotient d N hN a.family)
    (OrdinaryOddQuotient.blockEquiv d N hN)
    (OrdinaryOddQuotient.blockEquiv_character d N hN)
    (fun j g hg => inflateQuotientRepresentation_brauerValue d N (a.family.rep j) g hg)

@[simp] theorem PrincipalDecompositionData.ofOddQuotient_degree
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {n : ℕ}
    (a : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d N) n) :
    (a.ofOddQuotient d N hN).family.degree = a.family.degree := rfl

/-- Every entry of the actual Cartan matrix is preserved by an odd normal quotient. -/
@[simp] theorem PrincipalDecompositionData.ofOddQuotient_cartan
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {n : ℕ}
    (a : PrincipalDecompositionData (compatibleQuotientPrincipalCongruenceBlockData d N) n)
    (j k : Fin n) : (a.ofOddQuotient d N hN).cartan j k = a.cartan j k :=
  PrincipalDecompositionData.ofQuotientCorrespondence_cartan d N a
    (.ofOddQuotient d N hN a.family)
    (OrdinaryOddQuotient.blockEquiv d N hN)
    (OrdinaryOddQuotient.blockEquiv_character d N hN)
    (fun j g hg => inflateQuotientRepresentation_brauerValue d N (a.family.rep j) g hg) j k

end ModularBlock.Cartan
