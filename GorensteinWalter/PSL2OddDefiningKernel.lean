module

public import Theory.FieldTheory.SquareInvariantBiadditive
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import GorensteinWalter.PSL2RootSylow
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Excluding the defining prime from odd PSL₂ covering kernels

For a finite field of odd order q > 3, q ≠ 9, the defining prime does not
divide the kernel of any finite perfect central cover of the actual matrix
PSL₂(q). In particular it does not divide the kernel of the constructed
universal projection.

For q > 9, the commutator pairing of lifts of the upper root group is
additive and invariant under simultaneous multiplication by squares,
because conjugation by a lifted diagonal matrix fixes central commutators.
The finite-field polynomial argument makes this pairing zero. Thus the
Sylow preimage is abelian, and central Sylow transfer excludes the defining
prime from the kernel. Orders five and seven use cyclic Sylow transfer.
The exceptional order nine is retained throughout the final statements.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.1.3(1),(3), I.1.4(1), printed pp.407–408 / PDF pp.418–419, citing GLS3
§6.1 (canonical and exceptional multiplier tables). This proves the
remaining defining-prime premise consumed by
`PSL2Cover.isUniversal_of_defining_prime_not_dvd`.
-/

open scoped MatrixGroups commutatorElement IsMulCommutative

namespace GorensteinWalter.PSL2Cover

variable (F : Type*) [Field F] [Finite F]

/-- The full preimage of the standard defining root group is abelian in
every central extension when the odd field has more than nine elements. -/
public theorem root_preimage_abelian_of_card_gt_nine
    {E : Type*} [Group E] (f : E →* PSL(2, F))
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E)
    (h2 : (2 : F) ≠ 0) (hcard : 9 < Nat.card F) :
    IsMulCommutative ((psl2UpperUnipotentSubgroup F).comap f) := by
  obtain ⟨B, hB⟩ := CentralExtension.exists_lift_commutator_pairing f hf hker
    (psl2UpperUnipotentHom F)
  have htorus (a : F) (ha : a ≠ 0) (x : F) :
      psl2QuotientMap F (Matrix.SpecialLinearGroup.diag2 a ha) *
        psl2UpperUnipotentHom F (Multiplicative.ofAdd x) *
        (psl2QuotientMap F (Matrix.SpecialLinearGroup.diag2 a ha))⁻¹ =
      psl2UpperUnipotentHom F (Multiplicative.ofAdd (a^2*x)) := by
    change psl2QuotientMap F (Matrix.SpecialLinearGroup.diag2 a ha) *
      psl2QuotientMap F (sl2UpperUnipotent x) *
      (psl2QuotientMap F (Matrix.SpecialLinearGroup.diag2 a ha))⁻¹ =
      psl2QuotientMap F (sl2UpperUnipotent (a^2*x))
    rw [← map_inv, ← map_mul, ← map_mul]
    have hd : Matrix.SpecialLinearGroup.diag2 a ha ∈ sl2Borel F := by
      rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
      simp [Matrix.SpecialLinearGroup.diag2_coe']
    rw [sl2Borel_conj_upperUnipotent hd]
    simp [Matrix.SpecialLinearGroup.diag2_coe']
  have hinv (a : F) (ha : a ≠ 0) (x y : F) :
      B (a^2*x) (a^2*y) = B x y := by
    obtain ⟨X, hX⟩ := hf (psl2UpperUnipotentHom F (Multiplicative.ofAdd x))
    obtain ⟨Y, hY⟩ := hf (psl2UpperUnipotentHom F (Multiplicative.ofAdd y))
    obtain ⟨t, ht⟩ := hf (psl2QuotientMap F (Matrix.SpecialLinearGroup.diag2 a ha))
    have hXt : f (t*X*t⁻¹) =
        psl2UpperUnipotentHom F (Multiplicative.ofAdd (a^2*x)) := by
      rw [map_mul, map_mul, map_inv, ht, hX]
      exact htorus a ha x
    have hYt : f (t*Y*t⁻¹) =
        psl2UpperUnipotentHom F (Multiplicative.ofAdd (a^2*y)) := by
      rw [map_mul, map_mul, map_inv, ht, hY]
      exact htorus a ha y
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hB _ _ _ _ hXt hYt, hB _ _ _ _ hX hY, ← conjugate_commutatorElement]
    have hc : ⁅X,Y⁆ ∈ Subgroup.center E := by
      rw [← hB _ _ _ _ hX hY]
      exact (B x y).toMul.property
    rw [Subgroup.mem_center_iff.mp hc t]
    simp [mul_assoc]
  have hzero := FiniteField.biadditive_eq_zero_of_square_invariant h2 hcard B hinv
  refine ⟨⟨?_⟩⟩
  intro X Y
  apply Subtype.ext
  apply commutatorElement_eq_one_iff_mul_comm.mp
  obtain ⟨x, hx⟩ := X.property
  obtain ⟨y, hy⟩ := Y.property
  rw [← hB x.toAdd y.toAdd X Y hx.symm hy.symm, hzero]
  rfl

/-- Defining-characteristic kernel exclusion for every finite perfect
central cover of odd PSL₂(q), with q > 3 and q ≠ 9. -/
public theorem defining_prime_not_dvd_kernel
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E PSL(2, F))
    (hodd : Odd (Nat.card F)) (hcard : 3 < Nat.card F) (h9 : Nat.card F ≠ 9) :
    ¬ ringChar F ∣ Nat.card f.toMonoidHom.ker := by
  let : Fintype F := Fintype.ofFinite F
  let : Group.IsPerfect E := f.isPerfect
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  let : Fact (ringChar F).Prime := ⟨hp⟩
  have hFcard : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  by_cases hsmall : Nat.card F ≤ 9
  · have hprime : (Nat.card F).Prime := by
      have hcases : Nat.card F = 5 ∨ Nat.card F = 7 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rcases hcases with h | h <;> rw [h] <;> decide
    let : Fact (Nat.card F).Prime := ⟨hprime⟩
    apply f.not_dvd_card_multiplier_of_isCyclic_sylow
    intro Q
    obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hFcard Q
    let : IsCyclic (Multiplicative F) := isCyclic_of_prime_card (p := Nat.card F) rfl
    exact e.isCyclic.mp inferInstance
  · have h2 : (2 : F) ≠ 0 := by
      apply Ring.two_ne_zero
      intro hc
      have heven := FiniteField.even_card_of_char_two (F := F) hc
      have hodd' : Odd (Fintype.card F) := by
        simpa only [Nat.card_eq_fintype_card] using hodd
      exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_iff.mpr heven)
    obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow F hFcard
    apply PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow_preimage
      f.toMonoidHom f.surjective f.ker_le_center Q
    rw [hQ]
    exact root_preimage_abelian_of_card_gt_nine F f.toMonoidHom f.surjective
      f.ker_le_center h2 (by omega)

/-- The defining prime is absent from the actual universal covering kernel
of odd PSL₂(q), except for the excluded order-nine case. -/
public theorem defining_prime_not_dvd_universal_kernel
    (hodd : Odd (Nat.card F)) (hcard : 3 < Nat.card F) (h9 : Nat.card F ≠ 9) :
    ¬ ringChar F ∣ Nat.card (PerfectCentralCovering.universalProjection PSL(2, F)).ker := by
  let : Group.IsPerfect PSL(2, F) := psl2_isPerfect_of_card_gt_three F hcard
  exact defining_prime_not_dvd_kernel F (PerfectCentralCovering.universalCover PSL(2, F))
    hodd hcard h9

end GorensteinWalter.PSL2Cover
