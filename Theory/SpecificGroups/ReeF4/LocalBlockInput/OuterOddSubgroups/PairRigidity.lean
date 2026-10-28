module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters

/-!
# Inner–field rigidity for the standard Ree unipotent pair

For `m ≥ 1`, a pair-preserving automorphism of the supplied simple, perfect
fixed group is inner times a power of canonical Frobenius, assuming the
positive unipotent subgroup has odd index. The parabolic geometry recognizes
each signed simple block from the pair, and the root relations recover one
coefficient-field action after conjugation by an actual fixed-group element.

Every automorphism of the finite coefficient field is a power of squaring.
Matrix extensionality identifies the adjusted automorphism with that power
on each block, and generation by the four fixed blocks extends the equality
to the whole group. The final theorem discharges block recognition,
generation, parameter recovery and torus realization using `BlockGeometry`
and `BlockParameters`. Pair preservation and odd index remain explicit inputs.

Source: GLS3, 2.3.8(e), 2.5.1(b,c), and 2.5.12(d,f). The coefficient field
has order `2^(2*m+1)`. This is the pair-rigidity step of the outer restriction
used in Aschbacher–Smith, Remark A.2.4 and the proof of 1.3.4, printed pp.33
and 510 of `refs/quasithin.pdf`.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity

open Theory.AlgebraicGroup
variable {m : ℕ}

/-- An automorphism of the concrete coefficient field is a power of squaring. -/
theorem coefficientEquiv_eq_pow (m : ℕ)
    (σ : CoefficientField m ≃+* CoefficientField m) :
    ∃ n : ℕ, ∀ t : CoefficientField m, σ t = t ^ (2 ^ n) := by
  let σ' : CoefficientField m ≃ₐ[ZMod 2] CoefficientField m :=
    AlgEquiv.ofRingEquiv (f := σ) (fun t =>
      DFunLike.congr_fun (Subsingleton.elim
        (σ.toRingHom.comp (algebraMap (ZMod 2) (CoefficientField m)))
        (algebraMap (ZMod 2) (CoefficientField m))) t)
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ZMod 2) (CoefficientField m)).surjective σ'
  refine ⟨n.val, fun t => ?_⟩
  change σ' t = t ^ (2 ^ n.val)
  have ht := DFunLike.congr_fun hn t
  simpa only [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, ZMod.card] using ht.symm

/-- The matrix-entry formula for every nonnegative power of canonical Frobenius. -/
theorem fieldAutomorphism_pow_entry (d : LocalBlockInput m) (n : ℕ)
    (x : d.fixedGroup) (i j : F4Chevalley.BasisIndex) :
    (((d.fieldAutomorphism ^ n) x).val.val : MatrixCarrier m) i j =
      (x.val.val : MatrixCarrier m) i j ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, d.fieldAutomorphism_entry, ih,
      pow_succ 2 n, pow_mul]

/-- Convert a common field action on generating fixed blocks into the desired
inner–field expression. Both geometric inputs are explicit. -/
theorem inner_field_of_simpleBlock_entries (d : LocalBlockInput m)
    (hgen : (⨆ s, ⨆ positive, simpleBlock d s positive) = ⊤)
    (a : MulAut d.fixedGroup) (g : d.fixedGroup)
    (σ : CoefficientField m ≃+* CoefficientField m)
    (hentries : ∀ s positive, ∀ x ∈ simpleBlock d s positive,
      ∀ i j : F4Chevalley.BasisIndex,
        ((((MulAut.conj g)⁻¹ * a) x).val.val : MatrixCarrier m) i j =
          σ ((x.val.val : MatrixCarrier m) i j)) :
    ∃ n : ℤ, a = MulAut.conj g * d.fieldAutomorphism ^ n := by
  obtain ⟨n, hn⟩ := coefficientEquiv_eq_pow m σ
  have he : ((MulAut.conj g)⁻¹ * a).toMonoidHom =
      (d.fieldAutomorphism ^ n).toMonoidHom := by
    apply hom_ext_of_simpleBlocks_generate d hgen
    intro s positive x hx
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    change ((((MulAut.conj g)⁻¹ * a) x).val.val : MatrixCarrier m) i j =
      (((d.fieldAutomorphism ^ n) x).val.val : MatrixCarrier m) i j
    rw [hentries s positive x hx i j, hn, fieldAutomorphism_pow_entry]
  have he' : (MulAut.conj g)⁻¹ * a = d.fieldAutomorphism ^ n :=
    MulEquiv.ext fun x => DFunLike.congr_fun he x
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (inv_mul_eq_iff_eq_mul.mp he')

/-- Every automorphism preserving the actual positive and negative unipotent
subgroups is inner times a power of canonical Frobenius. Block recognition,
the common field action after inner adjustment, and fixed-block generation
are all derived; the odd unipotent index is the caller's explicit input. -/
theorem inner_field_of_preservesUnipotentPair (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hindex : Odd (LargeLocalSeeds.standardUnipotent d).index)
    (a : MulAut d.fixedGroup) (hp : d.PreservesUnipotentPair a) :
    ∃ (g : d.fixedGroup) (n : ℤ), a = MulAut.conj g * d.fieldAutomorphism ^ n := by
  have hb := preservesSimpleBlocks_of_preservesUnipotentPair hm d hindex a hp
  obtain ⟨g, σ, hentries⟩ := BlockParameters.exists_simpleBlock_entries hm d hindex a hp hb
  obtain ⟨n, hn⟩ := inner_field_of_simpleBlock_entries d (simpleBlocks_generate hm d)
    a g σ hentries
  exact ⟨g, n, hn⟩

end ReeF4.LocalBlockInput.PairRigidity
end
