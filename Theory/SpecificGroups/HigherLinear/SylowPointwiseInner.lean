module

public import Theory.SpecificGroups.HigherLinear.SylowPointwiseInner.Coordinates
public import Theory.SpecificGroups.HigherLinear.SylowPointwiseInner.UpperRoots
public import Theory.GroupAction.SylowPointwiseInner
/-!
# Arbitrary Sylow fixers reduced to projective reconstruction

The positive-root subgroup is a two-group and therefore lies in a Sylow
subgroup. The standard matrix calculation supplies inner implementers in
that root subgroup. Sylow conjugacy then transports both the automorphism
and its implementer to an arbitrary specified Sylow subgroup.

The remaining geometric input is explicit: an automorphism fixing the
positive roots pointwise must admit one of the linear-field or
linear-field-graph forms. The present module does not assert or conceal
that reconstruction theorem. Once it is proved, no additional Sylow,
order, simplicity, field, diagonal, or graph calculation is needed here.

Source: the type-A Sylow-centralizer fact in Aschbacher–Smith, B.1.13,
printed p.74, with standard actions as in GLS III, Theorem 2.5.1 and §2.7.
-/

public section

open scoped MatrixGroups
namespace Matrix.HigherLinear.SylowPointwiseInner
variable {d : ℕ} {F : Type*} [Field F]
/-- Standard-form reconstruction for upper-root fixers is the only remaining
input to the arbitrary-Sylow conclusion. The positive root group need only
be contained in a Sylow subgroup; its maximality is not assumed. -/
theorem fixing_sylow_inner_of_root_coverage [Finite F] [CharP F 2] (hd : 3 ≤ d)
    (hcoverage : ∀ a : MulAut PSL(d,F),
      (∀ x ∈ upperRoots d F, a x = x) → HasStandardForm d F a)
    (S : Sylow 2 PSL(d,F)) (a : MulAut PSL(d,F)) (ha : ∀ x ∈ S, a x = x) :
    ∃ z ∈ S, a = MulAut.conj z := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨P, hUP⟩ := (upperRoots_isPGroup (d := d) (F := F)).exists_le_sylow
  apply MulAut.fixing_inner_sylow P S _ a ha
  intro b hb
  have hbU : ∀ x ∈ upperRoots d F, b x = x := fun x hx => hb x (hUP hx)
  obtain ⟨z, hz, he⟩ := standard_fixes_upperRoots_inner hd b (hcoverage b hbU) hbU
  exact ⟨z, hUP hz, he⟩

/-- The pointwise fixer is exactly conjugation by the relative Sylow center,
under the same explicit geometric reconstruction premise. -/
theorem fixes_sylow_iff_center_conj_of_root_coverage [Finite F] [CharP F 2] (hd : 3 ≤ d)
    (hcoverage : ∀ a : MulAut PSL(d,F),
      (∀ x ∈ upperRoots d F, a x = x) → HasStandardForm d F a)
    (S : Sylow 2 PSL(d,F)) (a : MulAut PSL(d,F)) :
    (∀ x ∈ S, a x = x) ↔
      ∃ z ∈ (Subgroup.center S).map (S : Subgroup PSL(d,F)).subtype,
        a = MulAut.conj z := by
  constructor
  · intro ha
    obtain ⟨z, hz, he⟩ := fixing_sylow_inner_of_root_coverage hd hcoverage S a ha
    refine ⟨z, ?_, he⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro x
    apply Subtype.ext
    have hh := ha x x.property
    rw [he] at hh
    change z * (x : PSL(d,F)) * z⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩ x hx
    have hh : x * (z : PSL(d,F)) = (z : PSL(d,F)) * x :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)
    change (z : PSL(d,F)) * x * (z : PSL(d,F))⁻¹ = x
    rw [← hh, mul_inv_cancel_right]

end Matrix.HigherLinear.SylowPointwiseInner
