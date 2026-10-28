module

public import Theory.GroupTheory.Commutator.ScalarInvariantRoot
public import Theory.GroupTheory.Commutator.CentralAbelianSylow
public import GorensteinWalter.PSL2RootSylow
public import GorensteinWalter.SL2UniversalCover

/-!
# The defining-characteristic kernel for even PSL₂

For a finite field F of even order at least eight, every finite perfect central
extension of the actual matrix group PSL₂(F) has kernel of odd order. In
particular, the defining prime does not divide the kernel of its constructed
universal projection.

The standard upper root group is a Sylow subgroup. Diagonal matrices act on
its additive parameter by squares, and every field scalar is a square in
characteristic two. The scalar-invariant commutator-pairing theorem therefore
makes its full preimage abelian. Central Sylow transfer excludes two from the
kernel. Combining this exclusion with the existing cyclic-torus transfer
argument proves that the identity covering of PSL₂(F) is universal.

The field-size hypothesis is essential: at order four the universal cover
has kernel C₂. Source: the exhaustive multiplier lists in Aschbacher–Smith,
I.1.3–I.1.4, printed pp.407–408, and GLS III, Section 6.1 (Tables 6.1.2–6.1.3).
-/

open scoped MatrixGroups
namespace GorensteinWalter.PSL2Cover
universe u w
variable (F : Type u) [Field F] [Finite F]

private theorem upperUnipotent_full_scalar_action (heven : Even (Nat.card F)) :
    ∀ c : F, c ≠ 0 → ∃ t : PSL(2, F),
      ∀ x : F, t * psl2UpperUnipotentHom F (.ofAdd x) * t⁻¹ =
        psl2UpperUnipotentHom F (.ofAdd (c * x)) := by
  let : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr
    (by simpa only [← Nat.card_eq_fintype_card] using Nat.even_iff.mp heven)
  intro c hc
  obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two hchar c
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact hc ha
  let A := Matrix.SpecialLinearGroup.diag2 a ha0
  have hA : A ∈ sl2Borel F := by
    apply (sl2_mem_stabilizer_infinity_iff A).mpr
    simp [A, Matrix.SpecialLinearGroup.diag2_coe']
  refine ⟨psl2QuotientMap F A, fun x => ?_⟩
  change psl2QuotientMap F A * psl2QuotientMap F (sl2UpperUnipotent x) *
    (psl2QuotientMap F A)⁻¹ = psl2QuotientMap F (sl2UpperUnipotent (c * x))
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hA]
  have h00 : A.val 0 0 = a := rfl
  rw [h00, pow_two, ← ha]

/-- In even fields of order at least eight, lifts of upper-root elements
commute in every central extension of PSL₂. -/
public theorem upperUnipotent_preimage_commute_of_even {E : Type*} [Group E]
    (heven : Even (Nat.card F)) (hF : 8 ≤ Nat.card F)
    (f : E →* PSL(2, F)) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) {v w : E}
    (hv : f v ∈ psl2UpperUnipotentSubgroup F)
    (hw : f w ∈ psl2UpperUnipotentSubgroup F) : Commute v w := by
  let : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr
    (by simpa only [← Nat.card_eq_fintype_card] using Nat.even_iff.mp heven)
  let : CharP F 2 := ringChar.of_eq hchar
  exact CentralExtension.commute_lifts_of_full_scalar_action (by omega)
    f hf hk (psl2UpperUnipotentHom F) (upperUnipotent_full_scalar_action F heven) hv hw

/-- The defining prime is absent from the kernel of any finite perfect central
extension of matrix PSL₂ over an even field of order at least eight. -/
public theorem defining_prime_not_dvd_kernel_of_even {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (heven : Even (Nat.card F)) (hF : 8 ≤ Nat.card F)
    (f : E →* PSL(2, F)) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : ¬ ringChar F ∣ Nat.card f.ker := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  let : Fact (ringChar F).Prime := ⟨hp⟩
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow F hcard
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf (ringChar F) Q
  have hmap : (S : Subgroup E).map f = psl2UpperUnipotentSubgroup F := by
    rw [← Sylow.coe_mapSurjective hf, hS, hQ]
  apply CentralExtension.not_dvd_card_kernel_of_commutative_sylow f hk S
  intro v hv w hw
  apply upperUnipotent_preimage_commute_of_even F heven hF f hf hk
  · rw [← hmap]; exact Subgroup.mem_map_of_mem f hv
  · rw [← hmap]; exact Subgroup.mem_map_of_mem f hw

/-- The exact defining-prime exclusion for the constructed universal projection.
This discharges the remaining premise of the even-field identity-cover theorem. -/
public theorem defining_prime_not_dvd_universal_kernel_of_even (heven : Even (Nat.card F)) (hF : 8 ≤ Nat.card F) :
    ¬ ringChar F ∣ Nat.card (PerfectCentralCovering.universalProjection PSL(2, F)).ker := by
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  exact defining_prime_not_dvd_kernel_of_even F heven hF (PerfectCentralCovering.universalProjection PSL(2, F))
    (PerfectCentralCovering.universalProjection_surjective PSL(2, F))
    (PerfectCentralCovering.universalProjection_ker_le_center PSL(2, F))

/-- The actual identity covering is universal for every even field of order at
least eight. Both the torus-prime and defining-prime exclusions are discharged. -/
public theorem identity_isUniversal_of_even
    (heven : Even (Nat.card F)) (hF : 8 ≤ Nat.card F) :
    letI : Fact (3 < Nat.card F) := ⟨by omega⟩
    Theory.GroupTheory.Covering.IsUniversal.{u, u, w}
      (Theory.GroupTheory.Covering.id :
        Theory.GroupTheory.Covering PSL(2, F) PSL(2, F)) := by
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  exact identity_isUniversal_of_defining_prime_not_dvd F hF heven
    (defining_prime_not_dvd_universal_kernel_of_even F heven hF)

end GorensteinWalter.PSL2Cover
