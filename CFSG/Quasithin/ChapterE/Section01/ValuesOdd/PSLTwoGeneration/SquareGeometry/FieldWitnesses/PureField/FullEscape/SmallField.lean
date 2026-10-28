module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.FieldCentralizer
public import GorensteinWalter.LinearThreeEquiv
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.LocalSections

/-!
# The field-of-nine centralizer as an intrinsic E1 member

The marked centralizer is PGL₂(3) times the quadratic field-automorphism
group. The faithful projective-line action identifies its first factor with
S₄. Composing with the double-transposition action gives an actual surjection
to S₃ whose kernel is the intrinsic two-core of order eight.

An elementary actor containing the field involution has its ambient tau in
this centralizer. Nontrivial image in the specified S₃ quotient gives every
E1 clause and image rank exactly one. Extending a Sylow of the centralizer
to the ambient group proves existence with the literal Sylow intersection.
For a prescribed ambient Sylow that intersection remains an explicit input.
Arbitrary-family membership and escape from a prescribed proper overgroup
are separate geometric obligations retained by `FullEscape`.

The S₃ E1 adapter in the PSL₃ graph calculation is group-general; we apply
its exact quotient and kernel contract to this matrix centralizer.
Source: Aschbacher–Smith, E.1.2 and E.1.14(6), printed pp.209–210 and 214.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
variable {F : Type*} [Field F] [Finite F]

/-- The centralizer over the field of order nine, with its actual fixed-field
coordinate identified with S₄ by the projective-line action. -/
noncomputable def smallFieldCentralizerEquiv
    (hF : Nat.card F = 3 ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) :
    centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) ≃*
      Equiv.Perm (Fin 4) × (F ≃+* F) := by
  let K := FixedPoints.subfield (zpowers σ) F
  let := Fintype.ofFinite K
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
    (by simpa only [← Nat.card_eq_fintype_card] using fixedSubfield_card hF σ hsq hne)
  exact (fieldCentralizerEquiv Nat.prime_three hF σ hne).symm.trans
    (MulEquiv.prodCongr ((pgl2RingEquiv e).symm.trans pgl2_three_equiv_perm)
      (MulEquiv.refl _))

/-- The actual S₃ quotient is the S₄ double-transposition action after the
explicit fixed-field projection. -/
@[expose] noncomputable def smallFieldCentralizerQuotient
    (hF : Nat.card F = 3 ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) :
    centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) →*
      Equiv.Perm (Fin 3) :=
  Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom.comp
    ((MonoidHom.fst _ _).comp (smallFieldCentralizerEquiv hF σ hsq hne).toMonoidHom)

theorem smallFieldCentralizerQuotient_surjective
    (hF : Nat.card F = 3 ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) :
    Function.Surjective (smallFieldCentralizerQuotient hF σ hsq hne) := by
  intro y
  obtain ⟨x, rfl⟩ := Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective y
  obtain ⟨z, hz⟩ := (smallFieldCentralizerEquiv hF σ hsq hne).surjective (x, 1)
  refine ⟨z, ?_⟩
  change Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom
    ((smallFieldCentralizerEquiv hF σ hsq hne z).1) = _
  rw [hz]

variable [Finite (PGammaL2 F)]

/-- The field-involution centralizer has two-core of order eight; this
identifies the kernel of the specified S₃ map with the intrinsic two-core. -/
theorem smallFieldCentralizerQuotient_kernel
    (hF : Nat.card F = 3 ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) :
    (smallFieldCentralizerQuotient hF σ hsq hne).ker =
      pCore 2 (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))) ∧
    Nat.card (smallFieldCentralizerQuotient hF σ hsq hne).ker = 8 := by
  let f := smallFieldCentralizerQuotient hF σ hsq hne
  have hf := smallFieldCentralizerQuotient_surjective hF σ hsq hne
  have hC : Nat.card (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))) = 48 := by
    rw [Nat.card_congr (smallFieldCentralizerEquiv hF σ hsq hne).toEquiv,
      Nat.card_prod, FiniteField.card_ringAut_of_card_prime_pow Nat.prime_three hF]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hk : Nat.card f.ker = 8 := by
    have hh := f.ker.card_eq_card_quotient_mul_card_subgroup
    rw [hC, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at hh
    have h3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [h3] at hh
    omega
  exact ⟨ker_eq_twoCore_of_surjective_perm_three f hf
    (IsPGroup.of_card (n := 3) (by simpa using hk)), hk⟩

/-- A small-field centralizer is an E1 member for every elementary actor
containing σ with nontrivial image in its specified S₃ quotient. The remaining
geometric input is the literal Sylow intersection, not an abstract Sylow. -/
theorem isEMemberAt_smallFieldCentralizer
    (hF : Nat.card F = 3 ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup (PGammaL2 F)))
    (hσA : SemidirectProduct.inr σ ∈ A)
    (hSyl : ∃ U : Sylow 2 (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))),
      (U : Subgroup _) = (T : Subgroup (PGammaL2 F)).subgroupOf
        (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))))
    (ha : ¬ A.subgroupOf (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))) ≤
      (smallFieldCentralizerQuotient hF σ hsq hne).ker) :
    IsEMemberAt 1 (T : Subgroup (PGammaL2 F)) A
      (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))) := by
  let := hA
  have hAC : A ≤ centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) :=
    (Subgroup.le_centralizer A).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hσA))
  have htau : tau (T : Subgroup (PGammaL2 F)) A ≤
      centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) := by
    rw [full_tau_eq_inf_centralizer Nat.prime_three (by decide) hF (by decide)]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hx.2 _ hσA).symm)
  apply PSLThreeGeneration.ProperExtension.GraphThree.isEMemberAt_of_symmetricThree_quotient
    (T : Subgroup (PGammaL2 F)) A _ hA hAT hAC htau hSyl
    (smallFieldCentralizerQuotient hF σ hsq hne)
    (smallFieldCentralizerQuotient_surjective hF σ hsq hne) _ ha
  rw [(smallFieldCentralizerQuotient_kernel hF σ hsq hne).1]
  exact pCore_isPGroup

/-- Choose a genuine ambient Sylow with the required centralizer intersection.
Thus the small-field local member exists without a Sylow-placement premise;
its placement relative to a specified proper overgroup remains separate. -/
theorem exists_sylow_smallFieldCentralizer_member
    (hF : Nat.card F = 3 ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (A : Subgroup (PGammaL2 F)) (hA : IsElementaryAbelian 2 A)
    (hσA : SemidirectProduct.inr σ ∈ A)
    (ha : ¬ A.subgroupOf (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))) ≤
      (smallFieldCentralizerQuotient hF σ hsq hne).ker) :
    ∃ T : Sylow 2 (PGammaL2 F), IsEMemberAt 1 (T : Subgroup (PGammaL2 F)) A
      (centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))) := by
  let := hA
  let C := centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F))
  have hAC : A ≤ C := (Subgroup.le_centralizer A).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hσA))
  let : IsElementaryAbelian 2 (A.subgroupOf C) := IsElementaryAbelian.subgroupOf hAC
  obtain ⟨U, hAU⟩ := (IsElementaryAbelian.isPGroup 2 (A.subgroupOf C)).exists_le_sylow
  obtain ⟨T, hT⟩ := U.exists_comap_subtype_eq
  have hAT : A ≤ (T : Subgroup (PGammaL2 F)) := by
    intro x hx
    have hxU : (⟨x, hAC hx⟩ : C) ∈ (U : Subgroup C) := hAU hx
    rw [← hT] at hxU
    exact hxU
  exact ⟨T, isEMemberAt_smallFieldCentralizer hF σ hsq hne T A hA hAT hσA
    ⟨U, hT.symm⟩ ha⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
