module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Mathlib.GroupTheory.Index

/-!
# The diagonal torus acting on the Ree root subgroups

The integral F₄ torus acts diagonally on the Cartan-plus-root lattice, and its
proved conjugation formula scales each root-curve parameter. Its matrix image,
intersected with the actual split group, therefore normalizes the positive
subgroup and both root-generated local seeds. The parameter group is a product
of multiplicative groups of the even-order coefficient field, so this diagonal
torus has odd order.

The coroot-word torus in `RootData.lean` is left unchanged. Identifying its
words with these diagonal matrices is a separate obligation; the final lemmas
show exactly how that identification supplies its required geometry.

Source: the integral Chevalley torus action in Steinberg's root construction,
used for Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of
`refs/quasithin.pdf`.
-/

@[expose] public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup

namespace ReeF4.Parabolics
open LargeLocalSeeds
noncomputable section

/-- The four simple-coroot parameters of the integral diagonal action. -/
abbrev TorusParameter (m : ℕ) :=
  IntegralChevalleyTorusParameter (b := typeF4RootPairing_base) (CoefficientField m)

/-- The already constructed diagonal action on the Cartan-plus-root lattice. -/
def diagonalTorusHom (m : ℕ) : TorusParameter m →* MatrixUnits m where
  toFun := F4Chevalley.torusConjugation.torusElement
  map_one' := F4Chevalley.torusConjugation.torus_one
  map_mul' := F4Chevalley.torusConjugation.torus_mul

@[simp] theorem diagonalTorusHom_apply (m : ℕ) (u : TorusParameter m) :
    diagonalTorusHom m u = F4Chevalley.torusConjugation.torusElement u := rfl

/-- Diagonal torus matrices that lie in the concrete split carrier.
Equality with the coroot-word torus requires a separate word calculation. -/
def diagonalTorus (m : ℕ) : Subgroup (SplitGroup m) :=
  (diagonalTorusHom m).range.comap (SplitGroup m).subtype

/-- Every torus parameter is a tuple of nonzero elements of an even-order field. -/
theorem torusParameter_odd_card (m : ℕ) : Odd (Nat.card (TorusParameter m)) := by
  change Odd (Nat.card (typeF4RootPairing_base.support → (CoefficientField m)ˣ))
  rw [Nat.card_fun, Nat.card_units, field_card]
  have ho : Odd (2 ^ (2 * m + 1) - 1) := by
    refine ⟨2 ^ (2 * m) - 1, ?_⟩
    rw [pow_succ]
    have hp : 0 < 2 ^ (2 * m) := by positivity
    omega
  exact ho.pow

/-- The diagonal torus in the split carrier has odd order. -/
theorem diagonalTorus_odd_card (m : ℕ) : Odd (Nat.card (diagonalTorus m)) := by
  have hr := (torusParameter_odd_card m).of_dvd_nat (card_range_dvd (diagonalTorusHom m))
  let f : diagonalTorus m →* (diagonalTorusHom m).range :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply hr.of_dvd_nat (card_dvd_of_injective f ?_)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (diagonalTorusHom m).range => (z : MatrixUnits m)) h

private theorem diagonalTorus_normalizes_rootClosure (m : ℕ) (R : Set F4Chevalley.Root) :
    diagonalTorus m ≤ normalizer
      (closure {x | ∃ r t, r ∈ R ∧ x = rootGeneratorInGroup m r t} : Subgroup (SplitGroup m)) := by
  rw [le_normalizer_iff]
  intro z hz x hx
  change z.val ∈ (diagonalTorusHom m).range at hz
  obtain ⟨u, hu⟩ := hz
  change (MulAut.conj z) x ∈ _
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨r, ((integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r :
      (CoefficientField m)ˣ) : CoefficientField m) * t, hr, ?_⟩
    apply Subtype.ext
    change z.val * F4Chevalley.rootCurve r t * z.val⁻¹ = _
    rw [← hu]
    have he := F4Chevalley.rootCurve_torus_conjugation u⁻¹ r t
    simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe] using he
  | one => simpa only [map_one] using (one_mem _)
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using inv_mem hx

/-- Diagonal conjugation scales each positive root parameter. -/
theorem diagonalTorus_le_unipotent_normalizer (m : ℕ) :
    diagonalTorus m ≤ normalizer (splitUnipotent m : Set (SplitGroup m)) :=
  diagonalTorus_normalizes_rootClosure m {r | typeF4RootPairing_base.IsPos r}

/-- Diagonal conjugation preserves the root support of either seed. -/
theorem diagonalTorus_le_seed_normalizer (m : ℕ) (s : Side) :
    diagonalTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)) :=
  diagonalTorus_normalizes_rootClosure m {r | IsSeedRoot s r}

theorem splitTorus_le_diagonalTorus_of_words (m : ℕ)
    (hw : ∀ r t, torusWord m r t ∈ diagonalTorus m) :
    splitTorus m ≤ diagonalTorus m := by
  apply (closure_le _).mpr
  rintro x ⟨r, t, rfl⟩
  exact hw r t

theorem splitTorus_odd_card_of_le_diagonalTorus (m : ℕ)
    (hT : splitTorus m ≤ diagonalTorus m) : Odd (Nat.card (splitTorus m)) :=
  (diagonalTorus_odd_card m).of_dvd_nat (card_dvd_of_le hT)

theorem splitTorus_le_unipotent_normalizer_of_le_diagonalTorus (m : ℕ)
    (hT : splitTorus m ≤ diagonalTorus m) :
    splitTorus m ≤ normalizer (splitUnipotent m : Set (SplitGroup m)) :=
  hT.trans (diagonalTorus_le_unipotent_normalizer m)

theorem splitTorus_le_seed_normalizer_of_le_diagonalTorus (m : ℕ) (s : Side)
    (hT : splitTorus m ≤ diagonalTorus m) :
    splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)) :=
  hT.trans (diagonalTorus_le_seed_normalizer m s)

end
end ReeF4.Parabolics
