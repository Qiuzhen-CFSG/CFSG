module
public import Theory.Representation.OrthogonalFourMinusRankOne.LocalGeometry
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanFixed
public import Theory.Representation.SL2NaturalOffenders.Ratios.FixedLine
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# The Borel fixed space in the Hermitian SL₂ module

All upper roots force a fixed Hermitian matrix onto its upper singular line:
the off-diagonal entry vanishes by the nondegenerate quadratic-field trace.
A nonidentity element of the fixed-field torus moves that line when the fixed
field has more than two elements. Thus the actual Sylow normalizer has zero
fixed space for half-degree greater than one. The half-degree-one endpoint
is deliberately retained.

The terminal component sieve applies this to the orthogonal branch of the
PSL₂ module classifier, on the original quotient action.
Source: Aschbacher--Smith K.3.1(2), pp.453--454; 14.6.20, p.1037.
-/

public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup Representation Representation.BinaryOffender
namespace Representation.OrthogonalFourMinus.BorelFixed
open FiniteModel RankOne CartanFixed
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- Above the binary half-field, no nonzero Hermitian vector is Borel-fixed. -/
theorem fixedSpace_eq_bot (hs : 1 < s) :
    fixedSpace (SL2.BinarySmall.hermitian s) (rankOneBorel (Field s)) = ⊥ := by
  apply bot_unique
  intro X hX
  have hroot (u : Field s) : action s (upper s u) X = X :=
    hX ⟨upper s u, (mem_rankOneBorel_iff _).mpr (by simp [upper, transvection_coe])⟩
  have h1 := (root_fixed_iff s one_ne_zero X).mp (hroot 1)
  have hzfix : conjugation s (X.val 0 1) = X.val 0 1 := by
    simpa using CharTwo.add_eq_zero.mp h1.2
  obtain ⟨u,hu⟩ := exists_conjugation_ne s
  have hu0 : u ≠ 0 := by intro h; apply hu; simp [h]
  have hz : X.val 0 1 = 0 := by
    have he := ((root_fixed_iff s hu0 X).mp (hroot u)).2
    rw [hzfix, ← add_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (by
      intro heq
      exact hu ((CharTwo.add_eq_zero.mp heq).symm))
  have hXroot : X = rootVector s ⟨X.val 0 0,entry_fixed s X 0⟩ := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · simpa [rootVector, coordinates_symm_val] using hz
    · simpa [rootVector, coordinates_symm_val, hz] using (entry_conjugate s X 1 0).symm
    · simpa [rootVector, coordinates_symm_val] using h1.1
  have hc : 1 < Nat.card (fixedField s)ˣ := by
    rw [Nat.card_units,card_fixedField]
    have hp : 4 ≤ 2 ^ s := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hs
    omega
  let : Nontrivial (fixedField s)ˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨a,ha⟩ := exists_ne (1 : (fixedField s)ˣ)
  let b : (Field s)ˣ := Units.map (fixedField s).subtype.toMonoidHom a
  have hb : (b : Field s) ≠ 1 := by
    intro he
    apply ha
    apply Units.ext
    apply Subtype.ext
    exact he
  have hbf : conjugation s (b : Field s) = b := (a : fixedField s).property
  have hd := hX ⟨CartanFixed.diagonal s b, (mem_rankOneBorel_iff _).mpr (by simp [CartanFixed.diagonal,diag2_coe'])⟩
  change action s (CartanFixed.diagonal s b) X = X at hd
  rw [hXroot, diagonal_rootVector] at hd
  have he := congrArg (fun Y : Space s => Y.val 0 0) hd
  have hmul : ((b : Field s) * (b : Field s)) * X.val 0 0 = X.val 0 0 := by
    simpa [rootVector,coordinates_symm_val,FiniteModel.norm,hbf] using he
  have h00 : X.val 0 0 = 0 := by
    have he : ((b : Field s) ^ 2 - 1) * X.val 0 0 = 0 := by
      rw [sub_mul,one_mul,pow_two,hmul,sub_self]
    exact (mul_eq_zero.mp he).resolve_left (by
      intro h
      apply hb
      rcases sq_eq_one_iff.mp (sub_eq_zero.mp h) with hh | hh
      · exact hh
      · simpa only [CharTwo.neg_eq] using hh)
  rw [hXroot]
  change rootVector s ⟨X.val 0 0,_⟩ = 0
  have hz : (⟨X.val 0 0,entry_fixed s X 0⟩ : fixedField s) = 0 := Subtype.ext h00
  rw [hz]
  exact (coordinates s).symm.map_zero
end Representation.OrthogonalFourMinus.BorelFixed
