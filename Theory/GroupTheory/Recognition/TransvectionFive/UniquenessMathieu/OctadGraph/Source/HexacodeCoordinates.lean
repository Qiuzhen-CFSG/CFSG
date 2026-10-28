module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Quotient
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeAutomorphismPackage

/-!
# Source rectangle coordinates in the actual hexacode

An explicit binary change of basis identifies the source's eighteen exceptional
vectors with the eighteen hexacode words of weight six. Its inverse and weight
identity are checked on sixty-four vectors; addition is checked in six-bit
coordinates. Monomial hexacode automorphisms therefore act faithfully as source
exceptional symmetries. The six-four action bounds the latter group's order by
2160, equal to the proved hexacode automorphism order, giving equality of the
actual actions, including the cubic kernel.

The next source plane comparison uses this equivariant identification to
reconstruct its split extension. No quotient is replaced by a symmetric group,
and no marked intersection is inferred from an abstract group isomorphism.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4 and 41.4, pp.218, 222;
hexacode sextet geometry in 19.9, pp.96–97. The imported hexacode model is the
ATLAS port by Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research and
Attribution License 1.0; see `LICENSES/ATLAS.txt`.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource.PlaneComparison
open UniquenessLinear UniquenessLinear.PlaneTensor SourceNormalizer
open UniquenessLinear.PlaneCensus (Code)
open Atlas.Codes

private def bits (v : Fin 6 → Code) (x : Code) : Code :=
  (if x.getLsbD 0 then v 0 else 0) ^^^ (if x.getLsbD 1 then v 1 else 0) ^^^
  (if x.getLsbD 2 then v 2 else 0) ^^^ (if x.getLsbD 3 then v 3 else 0) ^^^
  (if x.getLsbD 4 then v 4 else 0) ^^^ (if x.getLsbD 5 then v 5 else 0)

private def changeBits : Code ≃ Code where
  toFun := bits ![10,63,62,57,45,28]
  invFun := bits ![6,57,51,56,43,29]
  left_inv := by decide
  right_inv := by decide

private theorem changeBits_xor : ∀ x y : Code,
    changeBits (x ^^^ y) = changeBits x ^^^ changeBits y := by decide

private def bitValue (b : Bool) : Bit := if b then 1 else 0

private def parameters (x : Code) : HexParameters :=
  (fun i => bitValue ((changeBits x).getLsbD i.val),
    fun i => bitValue ((changeBits x).getLsbD (3+i.val)),
    bitValue ((changeBits x).getLsbD 5))

private def parameterCode (t : HexParameters) : Code :=
  changeBits.symm (BitVec.cons (decide (t.2.2 = 1))
    (BitVec.cons (decide (t.2.1 1 = 1)) (BitVec.cons (decide (t.2.1 0 = 1))
    (BitVec.cons (decide (t.1 2 = 1)) (BitVec.cons (decide (t.1 1 = 1))
    (BitVec.cons (decide (t.1 0 = 1)) 0))))))

private theorem bitValue_decide (b : Bit) : bitValue (decide (b = 1)) = b := by
  revert b
  decide

private def parameterEquiv : Code ≃ HexParameters where
  toFun := parameters
  invFun := parameterCode
  left_inv := by decide
  right_inv t := by
    simp only [parameters,parameterCode,Equiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [BitVec.getElem_cons,bitValue_decide]
    · apply Prod.ext
      · funext i
        fin_cases i <;> simp [BitVec.getElem_cons,bitValue_decide]
      · simp [BitVec.getElem_cons,bitValue_decide]

private theorem bitValue_xor (b c : Bool) : bitValue (b ^^ c) = bitValue b + bitValue c := by
  cases b <;> cases c <;> decide

private theorem parameters_xor (x y : Code) : parameters (x ^^^ y) = parameters x + parameters y := by
  simp only [parameters, changeBits_xor, BitVec.getLsbD_xor, bitValue_xor]
  rfl

/-- Explicit coordinates identifying the 45-point rectangle with the hexacode. -/
def hexCoordinates : Code ≃ hexacode :=
  parameterEquiv.trans hexEquiv.toEquiv

theorem hexCoordinates_xor (x y : Code) :
    hexCoordinates (x ^^^ y) = hexCoordinates x + hexCoordinates y := by
  change hexEquiv (parameters (x ^^^ y)) = _
  rw [parameters_xor, map_add]
  rfl

theorem exceptional_iff_weight_six (x : Code) :
    Sextet.exceptional x = true ↔ hammingNorm (hexCoordinates x).val = 6 := by
  have h : ∀ x : Code, Sextet.exceptional x = true ↔
      hammingNorm (hexEncoder (parameters x)) = 6 := by decide
  exact h x

private def hexPermutation : HexAutomorphisms →* Equiv.Perm Code where
  toFun g := hexCoordinates.trans ((hexAction g).toEquiv.trans hexCoordinates.symm)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

private theorem hexPermutation_apply (g : HexAutomorphisms) (x : Code) :
    hexCoordinates (hexPermutation g x) = hexAction g (hexCoordinates x) :=
  hexCoordinates.apply_symm_apply _

private theorem hexPermutation_mem (g : HexAutomorphisms) :
    hexPermutation g ∈ Sextet.symmetryGroup := by
  rw [Sextet.mem_symmetryGroup]
  constructor
  · intro x y
    apply hexCoordinates.injective
    rw [hexCoordinates_xor, hexPermutation_apply, hexCoordinates_xor, map_add,
      hexPermutation_apply, hexPermutation_apply]
  · intro x
    apply Bool.eq_iff_iff.mpr
    rw [exceptional_iff_weight_six, exceptional_iff_weight_six, hexPermutation_apply]
    change hammingNorm (Monomial.act g.val (hexCoordinates x).val) = 6 ↔ _
    rw [Monomial.act_weight]

/-- The actual monomial hexacode action, in the source exceptional coordinates. -/
def hexSymmetry : HexAutomorphisms →* Sextet.symmetryGroup :=
  hexPermutation.codRestrict _ hexPermutation_mem

theorem hexSymmetry_action (g : HexAutomorphisms) (x : Code) :
    hexCoordinates ((hexSymmetry g).val x) = hexAction g (hexCoordinates x) :=
  hexPermutation_apply g x

theorem hexSymmetry_injective : Function.Injective hexSymmetry := by
  intro g h he
  apply hexAction_injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := hexCoordinates.surjective v
  rw [← hexSymmetry_action, ← hexSymmetry_action, he]

private theorem symmetry_card_le : Nat.card Sextet.symmetryGroup ≤ 2160 := by
  have hr := Nat.card_le_card_of_injective
    (fun x : Sextet.action.range => x.val) Subtype.val_injective
  have hs : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [hs] at hr
  have hm := card_eq_card_quotient_mul_card_subgroup Sextet.action.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Sextet.action).toEquiv] at hm
  rw [hm]
  exact (Nat.mul_le_mul hr Sextet.kernel_card_le).trans (by decide)

theorem hexSymmetry_bijective : Function.Bijective hexSymmetry :=
  hexSymmetry_injective.bijective_of_nat_card_le (by
    rw [hexAutomorphisms_card]
    exact symmetry_card_le)

/-- All source exceptional symmetries are actual hexacode monomial automorphisms. -/
def symmetryHexEquiv : Sextet.symmetryGroup ≃* HexAutomorphisms :=
  (MulEquiv.ofBijective hexSymmetry hexSymmetry_bijective).symm

theorem symmetryHexEquiv_action (f : Sextet.symmetryGroup) (x : Code) :
    hexCoordinates (f.val x) = hexAction (symmetryHexEquiv f) (hexCoordinates x) := by
  have hh := hexSymmetry_action (symmetryHexEquiv f) x
  have he : hexSymmetry (symmetryHexEquiv f) = f :=
    (MulEquiv.ofBijective hexSymmetry hexSymmetry_bijective).apply_symm_apply f
  rwa [he] at hh

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource.PlaneComparison
