module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FieldSubgroups
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.RootGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.Recognition
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity

/-!
# Common local actions from signed Ree root-block coordinates

A common field automorphism on the four signed root blocks is a single power
of Frobenius. Faithfulness of the actual matrix representation identifies the
corresponding group elements. Generation by the fixed blocks then extends that
agreement to the group, and in particular to both local seeds with the same
inner element and the same field exponent. Two successive inner adjustments
combine in the order in which they act.

This is the coordinate-to-local-action step of the automorphism argument in
GLS3, 2.5.1, used by Aschbacher--Smith F.1.12, printed pp.263--264 of
`refs/quasithin.pdf`. The source conventions are in
`refs/KGroup/GLS3/chapter2.tex`, Sections 2.4--2.5. The final theorem assembles
fixed-block generation, recognition after an inner adjustment, and the common
field-coordinate formula. It supplies compatible local actions for every
two-power automorphism normalizing the positive subgroup when `m ≥ 1`, retaining
only the supplied odd-index and seed-generation hypotheses. The coordinate
argument needs no order condition on either inner-adjusted automorphism.
No simplicity, perfectness, or automorphism-coverage assumption is used.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions

open LargeLocalSeeds Theory.AlgebraicGroup

/-- Every iterated canonical field automorphism raises each matrix entry to
the same power of two. -/
theorem fieldAutomorphism_pow_entry (m n : ℕ) (x : Model m)
    (i j : F4Chevalley.BasisIndex) :
    (matrixRepresentation m ((fieldAutomorphism m ^ n) x) : MatrixCarrier m) i j =
      (matrixRepresentation m x : MatrixCarrier m) i j ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, fieldAutomorphism_entry, ih,
      pow_succ 2 n, pow_mul]

/-- Agreement of the actual matrices on all four generating fixed blocks
identifies an automorphism with one inner-times-field expression. The field
exponent is chosen once, before restricting to any block. -/
theorem inner_field_of_simpleBlock_entries (m : ℕ)
    (hgen : (⨆ s, ⨆ positive, simpleBlock m s positive) = ⊤)
    (a : MulAut (Model m)) (g : Model m)
    (σ : CoefficientField m ≃+* CoefficientField m)
    (hentries : ∀ s positive, ∀ x ∈ simpleBlock m s positive,
      ∀ i j : F4Chevalley.BasisIndex,
        (matrixRepresentation m (((MulAut.conj g)⁻¹ * a) x) : MatrixCarrier m) i j =
          σ ((matrixRepresentation m x : MatrixCarrier m) i j)) :
    ∃ k : ℕ, a = MulAut.conj g * fieldAutomorphism m ^ k := by
  obtain ⟨k, hk⟩ := LocalBlockInput.PairRigidity.coefficientEquiv_eq_pow m σ
  have hblocks : ∀ s positive, Set.EqOn ((MulAut.conj g)⁻¹ * a)
      (fieldAutomorphism m ^ k : MulAut (Model m)) (simpleBlock m s positive) := by
    intro s positive x hx
    apply matrixRepresentation_injective m
    apply Units.ext
    apply Matrix.ext
    intro i j
    rw [hentries s positive x hx i j, hk, fieldAutomorphism_pow_entry]
  have hle : (⨆ s, ⨆ positive, simpleBlock m s positive) ≤
      ((MulAut.conj g)⁻¹ * a).toMonoidHom.eqLocus
        (fieldAutomorphism m ^ k).toMonoidHom :=
    iSup_le fun s => iSup_le fun positive => hblocks s positive
  have he : (MulAut.conj g)⁻¹ * a = fieldAutomorphism m ^ k := by
    apply MulEquiv.ext
    intro x
    exact hle (hgen ▸ Subgroup.mem_top x)
  exact ⟨k, inv_mul_eq_iff_eq_mul.mp he⟩

/-- A common coordinate formula after a geometric and a torus adjustment gives
one witness on both entire local seeds. Each occurrence of `simpleBlock` is an
actual fixed intersection, not merely a set of selected root words. -/
theorem local_actions_of_two_adjustments (m : ℕ)
    (hgen : (⨆ s, ⨆ positive, simpleBlock m s positive) = ⊤)
    (b : MulAut (Model m)) (g z : Model m)
    (σ : CoefficientField m ≃+* CoefficientField m)
    (hentries : ∀ s positive, ∀ x ∈ simpleBlock m s positive,
      ∀ i j : F4Chevalley.BasisIndex,
        (matrixRepresentation m
          (((MulAut.conj z)⁻¹ * ((MulAut.conj g)⁻¹ * b)) x) : MatrixCarrier m) i j =
          σ ((matrixRepresentation m x : MatrixCarrier m) i j)) :
    ∃ k : ℕ, ∀ s : Side,
      Set.EqOn b (MulAut.conj (g * z) * fieldAutomorphism m ^ k : MulAut (Model m))
        (seed m s) := by
  obtain ⟨k, hk⟩ := inner_field_of_simpleBlock_entries m hgen
    ((MulAut.conj g)⁻¹ * b) z σ hentries
  have hb : b = MulAut.conj (g * z) * fieldAutomorphism m ^ k := by
    rw [map_mul, mul_assoc]
    exact inv_mul_eq_iff_eq_mul.mp hk
  exact ⟨k, fun _ _ _ => DFunLike.congr_fun hb _⟩

/-- A normalized two-power automorphism has one common inner-times-field
expression on both root-defined local seeds. The geometric correction and the
fixed-torus correction combine as `g * z`; the exponent is recovered once from
their common field map. The local calculation itself does not need the
two-power equation, which is retained to match the innerness assembly's input.
Odd index and seed generation remain the caller's explicit hypotheses. -/
theorem exists_local_actions_of_normalized_twoPower (m : ℕ) (hm : 1 ≤ m)
    (hindex : Odd (unipotent m).index)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    (b : MulAut (Model m)) (r : ℕ) (_hb : b ^ (2 ^ r) = 1)
    (hU : (unipotent m).map b.toMonoidHom = unipotent m) :
    ∃ (x : Model m) (k : ℕ), ∀ s : Side,
      Set.EqOn b (MulAut.conj x * fieldAutomorphism m ^ k : MulAut (Model m))
        (seed m s) := by
  obtain ⟨g, hp, hc⟩ := exists_inner_adjustment_preserving_pair_and_blocks hm hindex b hU
  obtain ⟨z, σ, hentries⟩ := Semilinear.exists_common_field m hm hindex hgen
    ((MulAut.conj g)⁻¹ * b) hp hc
  obtain ⟨k, hk⟩ := local_actions_of_two_adjustments m (simpleBlocks_generate hm hgen)
    b g z σ hentries
  exact ⟨g * z, k, hk⟩

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
