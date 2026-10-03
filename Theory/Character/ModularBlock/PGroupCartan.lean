module

public import Theory.Character.ModularBlock.Cartan
public import Theory.Character.ModularBlock.ScalarAlgebra
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Principal Cartan data for finite two-groups

For every prescribed principal congruence datum of a finite two-group, the
unique simple modular representation is the one-dimensional trivial module.
A nonzero fixed vector gives an injective intertwiner from that module;
irreducibility makes it surjective. Its eigenvalue-defined Brauer character
therefore forms a complete singleton family in the actual principal block.

To identify the ordinary block, apply the same fixed-vector theorem to the
kernel of its reduced central selector in the regular representation.
Augmentation one forces this kernel to vanish, so the selector is one.
Reducing ordinary central scalars then shows that every ordinary irreducible
belongs to the prescribed block. Coefficient reconstruction at the identity
gives the sum of squared degrees, while the identity is the only odd-order
element. Thus decomposition coefficients are ordinary degrees and the genuine
Cartan matrix is the singleton matrix with entry the group order.

This supplies the two-group computations used in Fong, *Some Sylow subgroups
of order 32 and a characterization of U(3,3)*, J. Algebra 6 (1967), printed
p. 71, equations (6)–(7). The fixed-vector input is the existing theorem in
`Theory.Representation.TwoDimensionalOddOrder`; no block-membership or
matrix-existence hypothesis is imposed.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.PGroupCartan
variable {F G V : Type*} [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V]

omit [Finite G] in
private theorem algebra_apply_fixed (ρ : Representation F G V) (v : V)
    (hv : ∀ g, ρ g v = v) (a : MonoidAlgebra F G) :
    ρ.asAlgebraHom a v = groupAlgebraAugmentation F G a • v := by
  classical
  induction a using MonoidAlgebra.induction_on with
  | of g => simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, hv,
      groupAlgebraAugmentation_single]
  | add a b ha hb => simp [map_add, ha, hb, add_smul]
  | smul c a ha => simp [map_smul, ha, smul_smul]

private theorem central_idempotent_eq_one (hG : IsPGroup (ringChar F) G)
    (hc : ringChar F ≠ 0) (e : MonoidAlgebra F G)
    (he : e ∈ Set.center (MonoidAlgebra F G)) (hid : e * e = e)
    (haug : groupAlgebraAugmentation F G e = 1) : e = 1 := by
  classical
  let ρ := Representation.ofMulAction F G G
  let W : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (ρ.asAlgebraHom e)
      apply_mem_toSubmodule := by
        intro g v hv
        change ρ.asAlgebraHom e (ρ g v) = 0
        rw [← Representation.asAlgebraHom_single_one ρ g]
        change (ρ.asAlgebraHom e * ρ.asAlgebraHom (MonoidAlgebra.single g 1)) v = 0
        rw [← map_mul, (Semigroup.mem_center_iff.mp he _).symm, map_mul]
        change ρ.asAlgebraHom (MonoidAlgebra.single g 1) (ρ.asAlgebraHom e v) = 0
        rw [show ρ.asAlgebraHom e v = 0 from hv, map_zero] }
  by_contra hne
  have hm : (1 - e) ∈ W := by
    change ρ.asAlgebraHom e (1 - e) = 0
    rw [Representation.asAlgebraHom_ofMulAction_smul_eq_mul]
    simp [mul_sub, hid]
  let : Nontrivial W.toSubmodule := ⟨⟨⟨1 - e, hm⟩, 0, by
    intro h
    have hh : 1 - e = 0 := congrArg Subtype.val h
    exact hne (sub_eq_zero.mp hh).symm⟩⟩
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector hc hG W.toRepresentation
  have hfixed : ∀ g, ρ g v.val = v.val := fun g => congrArg Subtype.val (hfix g)
  have hvzero : v.val = 0 := by
    have h := algebra_apply_fixed ρ v.val hfixed e
    rw [haug, one_smul] at h
    exact h.symm.trans v.property
  exact hv (Subtype.ext hvzero)

omit [Finite G] in
private theorem singleton_irreducible :
    Representation.IsIrreducible (Representation.trivial F G (Fin 1 → F)) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  apply is_simple_module_of_finrank_eq_one (K := F)
  change Module.finrank F (Fin 1 → F) = 1
  simp

private theorem simple_equiv_trivial [FiniteDimensional F V]
    (hc : ringChar F ≠ 0) (hG : IsPGroup (ringChar F) G)
    (ρ : Representation F G V) [Representation.IsIrreducible ρ] :
    Nonempty (ρ.Equiv (Representation.trivial F G (Fin 1 → F))) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector hc hG ρ
  let f : Representation.IntertwiningMap (Representation.trivial F G (Fin 1 → F)) ρ :=
    { toLinearMap :=
        { toFun := fun x => x 0 • v
          map_add' := by intros; simp [add_smul]
          map_smul' := by intros; simp [smul_smul] }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        change x 0 • v = ρ g (x 0 • v)
        rw [map_smul, show ρ g v = v from hfix g] }
  have hf : f ≠ 0 := by
    intro h
    have hz := congrArg (fun q : Representation.IntertwiningMap
      (Representation.trivial F G (Fin 1 → F)) ρ => q (fun _ => 1)) h
    exact hv (by simpa [f] using hz)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hh : x 0 = y 0 := (smul_left_injective F hv) hxy
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa [hj] using hh
  have hsurj := (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  exact ⟨(f.ofBijective ⟨hinj, hsurj⟩).symm⟩

open PrincipalBlockConstruction BrauerBlockReduction BrauerCoefficientExtension
open BlockPrimitivity BlockOrthogonality
variable (d : PrincipalCongruenceBlockData G)

/-- The actual reduced principal selector of a finite two-group is the identity. -/
theorem reducedSelector_eq_one (hG : IsPGroup 2 G) :
    reducedPrincipalBlockElement d = 1 := by
  have hchar : ringChar (principalResidueField d) = 2 := ringChar.eq _ 2
  exact central_idempotent_eq_one (hchar.symm ▸ hG) (by omega) _
    (reducedPrincipalBlockElement_mem_center d)
    (reducedPrincipalBlockElement_isIdempotent d)
    (reducedPrincipalBlockElement_augmentation_eq_one d)

private theorem scalar_one (i : d.I) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec d.primeIdeal
      (d.chi i) (d.complete.1 i) 1 = 1 := by
  obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
  let : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (by simpa [hρ] using (d.complete.1 i).2)
  let : Nontrivial (Fin n → ℂ) := irreducible_nontrivial ρ
  apply localizationToComplex_injective d
  have h := localizedCentralScalar_action d i ρ hρ 1
  have hh : (1 : Module.End ℂ (Fin n → ℂ)) =
      localizationToComplex d.primeIdeal
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec d.primeIdeal
          (d.chi i) (d.complete.1 i) 1) • 1 := by
    simpa using h
  apply FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ (Fin n → ℂ))
  simpa [Algebra.algebraMap_eq_smul_one] using hh.symm

/-- Every ordinary irreducible belongs to the prescribed principal two-block. -/
theorem mem_block (hG : IsPGroup 2 G) (i : d.I) : i ∈ d.block := by
  classical
  let e : Subring.center (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) :=
    ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
      BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
  have hz : MonoidAlgebra.mapRingHom G (localizationToResidue d) (e - 1).val = 0 := by
    change MonoidAlgebra.mapRingHom G (localizationToResidue d)
      (BlockOrthogonality.localizedPrincipalBlockElement d - 1) = 0
    rw [map_sub, map_one]
    change reducedPrincipalBlockElement d - 1 = 0
    rw [reducedSelector_eq_one d hG, sub_self]
  have hs := localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero d i (e - 1) hz
  rw [localizedCentralScalar_sub, scalar_one,
    show CentralScalarCongruence.localizedCentralScalar d.eta_spec d.primeIdeal
      (d.chi i) (d.complete.1 i) e = if i ∈ d.block then 1 else 0 from
      localizedCentralScalar_localizedPrincipalBlockElement d i] at hs
  by_contra hi
  simp [hi] at hs

omit [Finite G] in
private theorem odd_eq_one (hG : IsPGroup 2 G) {g : G} (hg : Odd (orderOf g)) : g = 1 := by
  by_contra hne
  exact (Nat.not_even_iff_odd.mpr hg) (even_iff_two_dvd.mpr (hG.dvd_orderOf hne))

/-- The actual one-dimensional trivial representation over the prescribed splitting field. -/
@[expose] def trivialRep : Representation (splittingField d) G (Fin 1 → splittingField d) :=
  Representation.trivial _ _ _

/-- The prescribed principal selector acts identically on the actual trivial module. -/
theorem trivialRep_inBlock : Cartan.InPrincipalBlock d (trivialRep d) := by
  apply LinearMap.ext
  intro v
  rw [algebra_apply_fixed (trivialRep d) v (fun _ => rfl)]
  have haug : groupAlgebraAugmentation (splittingField d) G (Cartan.splittingSelector d) = 1 := by
    rw [Cartan.splittingSelector, groupAlgebraAugmentation_mapRingHom,
      reducedPrincipalBlockElement_augmentation_eq_one, map_one]
  rw [haug, one_smul, Module.End.one_apply]

/-- The complete singleton family of simple modules in the principal block of a two-group. -/
@[expose] def family (hG : IsPGroup 2 G) : Cartan.PrincipalBrauerFamily d 1 where
  degree := fun _ => 1
  rep := fun _ => trivialRep d
  irreducible := fun _ => by exact singleton_irreducible
  inBlock := fun _ => trivialRep_inBlock d
  complete := by
    intro m ρ hρ _
    let := hρ
    refine ⟨0, ?_⟩
    have hchar : ringChar (splittingField d) = 2 := ringChar.eq _ 2
    exact simple_equiv_trivial (by omega) (hchar.symm ▸ hG) ρ
  independent := by
    rw [linearIndependent_unique_iff]
    intro h
    have hv := congrFun h (BrauerCharacter.twoRegularClass (1 : G) (by simp))
    simp [BrauerCharacter.character_apply, BrauerCharacter.value_one] at hv

/-- The prescribed principal two-block exhausts the complete ordinary family. -/
theorem block_eq_univ (hG : IsPGroup 2 G) : d.block = Finset.univ := by
  classical
  exact Finset.eq_univ_iff_forall.mpr (mem_block d hG)

/-- The sum of squared ordinary degrees in the prescribed block is the group order. -/
theorem sum_degree_sq (hG : IsPGroup 2 G) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 = (Nat.card G : ℂ) := by
  classical
  rw [block_eq_univ d hG]
  have h := BlockOrthogonality.coeff_eq_inv_card_mul_sum_scalar_degree_character
    d.chi d.complete (1 : MonoidAlgebra ℂ G) (by simp) (fun _ => 1)
    (by intros; simp) 1
  have h' : (1 : ℂ) = (Nat.card G : ℂ)⁻¹ *
      ∑ i : d.I, d.chi i (ConjClasses.mk 1) ^ 2 := by
    simpa [pow_two] using h
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  simpa [hc, mul_assoc] using congrArg (fun z : ℂ => (Nat.card G : ℂ) * z) h'.symm

/-- The dimension of an ordinary representation affording the specified irreducible. -/
@[expose] def ordinaryDegree (i : d.I) : ℕ := (d.complete.1 i).1.choose

/-- The ordinary natural degree equals the character value at the identity. -/
theorem ordinaryDegree_eq (i : d.I) :
    d.chi i (ConjClasses.mk 1) = (ordinaryDegree d i : ℂ) := by
  obtain ⟨ρ, hρ⟩ := (d.complete.1 i).1.choose_spec
  rw [hρ]
  change ρ.character 1 = _
  simp [Representation.char_one, ordinaryDegree]

/-- Decomposition into the genuine trivial Brauer character, with ordinary degree coefficients. -/
@[expose] def decompositionData (hG : IsPGroup 2 G) : Cartan.PrincipalDecompositionData d 1 where
  family := family d hG
  decomposition := fun i _ => ordinaryDegree d i
  restriction := by
    intro i _ g hg
    rw [odd_eq_one hG hg, ordinaryDegree_eq d i]
    simp only [BrauerCharacter.value_one, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    simp [family]

/-- The sole simple module in the constructed decomposition datum has degree one. -/
theorem family_degree (hG : IsPGroup 2 G) : (decompositionData d hG).family.degree 0 = 1 := rfl

/-- The genuine singleton Cartan invariant is the order of the two-group. -/
theorem cartan_eq_card (hG : IsPGroup 2 G) :
    (decompositionData d hG).cartan 0 0 = Nat.card G := by
  have h := (decompositionData d hG).sum_degree_sq
  rw [sum_degree_sq d hG] at h
  have h' : (Nat.card G : ℂ) = ((decompositionData d hG).cartan 0 0 : ℂ) := by
    simpa [decompositionData, family] using h
  exact_mod_cast h'.symm

/-- Every prescribed datum of a finite two-group admits the genuine Cartan computation. -/
theorem exists_decompositionData (hG : IsPGroup 2 G) :
    ∃ a : Cartan.PrincipalDecompositionData d 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = Nat.card G :=
  ⟨decompositionData d hG, family_degree d hG, cartan_eq_card d hG⟩

end ModularBlock.PGroupCartan
