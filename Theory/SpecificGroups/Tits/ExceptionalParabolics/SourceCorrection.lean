module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The first-parabolic numerical discrepancy in F.1.12

The checked Parrott relations force the images of `r1` and `s1` to coincide
under every homomorphism from the first overgroup to the dihedral group of
order ten. The image is therefore already the image of its Sylow two-subgroup,
so such a homomorphism cannot be surjective.

The first overgroup has proved order 10240. The counting lemma below
therefore rules out the printed pair `|O₂(L₁)| = 1024`, `L₁/O₂(L₁) ≃ D₁₀`
for *every* subgroup `L₁ ≤ first`: those numbers force `L₁ = first`.
Distinguishing a smaller source `L₁` from the full parabolic cannot repair
that particular pair.
This does not yet calculate the actual two-core or quotient, nor rule out
smaller source subgroups with a dihedral quotient and a smaller two-core.

Sources: Aschbacher--Smith, F.1.12(I)(9), printed p. 263; Parrott (1972),
pp. 672 and 683. Parrott gives order 512 and Frobenius quotient of order 20
for the involution centralizer. Chapter 14, printed pp. 988--989, must likewise
be used with the actual local groups and maps, rather than the incompatible
numerical pair. The group alternatives are unaffected by this obstruction.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics

private theorem small_check : ∀ x y z : DihedralGroup 5,
    x ^ 2 = 1 → y ^ 2 = 1 → z ^ 4 = 1 →
    x⁻¹ * z⁻¹ * x * z = 1 → (x * y) ^ 5 = 1 →
    y * z * y * ((x * y) ^ 2 * z)⁻¹ = 1 → y = x := by
  decide +kernel

private theorem s1_mem : atlas1600ParrottAssignment .s1 ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  exact Subgroup.subset_closure (by simp)

private theorem s5_mem : atlas1600ParrottAssignment .s5 ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  exact Subgroup.subset_closure (by simp)

private abbrev x : first := ⟨atlas1600ParrottAssignment .s1, sylow_le_first s1_mem⟩
private abbrev y : first := ⟨atlas1600ParrottAssignment .r1, reflection_mem_first⟩
private abbrev z : first := ⟨atlas1600ParrottAssignment .s5, sylow_le_first s5_mem⟩

private theorem rels : x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ z ^ 4 = 1 ∧
    x⁻¹ * z⁻¹ * x * z = 1 ∧ (x * y) ^ 5 = 1 ∧
    y * z * y * ((x * y) ^ 2 * z)⁻¹ = 1 := by
  have h := atlas1600ParrottAssignment_relations
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply Subtype.ext
  · simpa [parrottRelator] using h .i_s1
  · simpa [parrottRelator] using h .i_r1
  · simpa [parrottRelator] using h .i_s5
  · simpa [parrottRelator, parrottCommutator] using h .ii_s1_s5
  · simpa [parrottRelator] using h .vi_s1_r1
  · simpa [parrottRelator] using h .vii_s5

private theorem image_eq (f : first →* DihedralGroup 5) : f y = f x := by
  have ⟨h1,h2,h3,h4,h5,h6⟩ := rels
  apply small_check (f x) (f y) (f z)
  all_goals first
    | simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h1
    | simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h2
    | simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h3
    | simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h4
    | simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h5
    | simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h6

private theorem sylow_image_surjective (f : first →* DihedralGroup 5)
    (hf : Function.Surjective f) :
    Function.Surjective (f.comp (Subgroup.inclusion sylow_le_first)) := by
  let φ := f.comp (Subgroup.inclusion sylow_le_first)
  let H : Subgroup Atlas1600Group := (φ.range.comap f).map first.subtype
  have hs : S ≤ H := by
    intro s hs
    refine ⟨⟨s, sylow_le_first hs⟩, ?_, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  have hr : atlas1600ParrottAssignment .r1 ∈ H := by
    refine ⟨y, ?_, rfl⟩
    exact ⟨⟨atlas1600ParrottAssignment .s1, s1_mem⟩, (image_eq f).symm⟩
  have hfirst : first ≤ H := by
    exact sup_le hs ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hr))
  intro d
  obtain ⟨a, ha⟩ := hf d
  obtain ⟨b, hb, hba⟩ := hfirst a.property
  have h : b = a := Subtype.ext hba
  subst b
  obtain ⟨s, hs⟩ := hb
  exact ⟨s, hs.trans ha⟩

/-- The full first parabolic has no quotient isomorphic to the dihedral group of order ten. -/
theorem first_no_dihedral_surjection (f : first →* DihedralGroup 5) : ¬ Function.Surjective f := by
  intro hf
  have hd := Subgroup.card_dvd_of_surjective
    (f.comp (Subgroup.inclusion sylow_le_first)) (sylow_image_surjective f hf)
  rw [DihedralGroup.nat_card, sylow_card] at hd
  norm_num at hd

/-- The obstruction holds for every intrinsic normal subgroup, not only the two-core. -/
theorem first_no_dihedral_quotient (N : Subgroup first) [N.Normal] :
    ¬ Nonempty ((first ⧸ N) ≃* DihedralGroup 5) := by
  rintro ⟨e⟩
  exact first_no_dihedral_surjection (e.toMonoidHom.comp (QuotientGroup.mk' N))
    (e.surjective.comp Quotient.mk''_surjective)

/-- Conditional counting obstruction for every possible marked subgroup.
The order premise remains a separate concrete calculation. -/
theorem no_printed_first_package_of_card (hcard : Nat.card first = 10240) (L : Subgroup Atlas1600Group)
    (hL : L ≤ first) (hcore : Nat.card (pCore 2 L) = 1024)
    (e : (L ⧸ pCore 2 L) ≃* DihedralGroup 5) : False := by
  have hquot : Nat.card (L ⧸ pCore 2 L) = 10 :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hLcard := (pCore 2 L).card_eq_card_quotient_mul_card_subgroup
  rw [hcore, hquot] at hLcard
  have heq : L = first := Subgroup.eq_of_le_of_card_ge hL (by omega)
  subst L
  exact first_no_dihedral_quotient (pCore 2 first) ⟨e⟩

/-- No choice of a local factor inside this full parabolic realizes the printed
first Tits package. This discharges the order premise of the counting obstruction. -/
theorem no_printed_first_package (L : Subgroup Atlas1600Group)
    (hL : L ≤ first) (hcore : Nat.card (pCore 2 L) = 1024)
    (e : (L ⧸ pCore 2 L) ≃* DihedralGroup 5) : False :=
  no_printed_first_package_of_card first_card L hL hcore e

end Tits.ExceptionalParabolics
