module

public import Theory.Representation.G2OrthogonalCover.HyperplaneStabilizers
public import Theory.Representation.G2OrthogonalCover.BinaryHyperplaneFixers
import all Theory.Representation.G2OrthogonalCover.HyperplaneOrbits

/-!
# A derived cubic normalizer moving a cover hyperplane

On the norm-zero orbit, the cubic commutator B fixes the seed hyperplane.
A short derived word in A and B inverts B and moves that hyperplane.
Conjugation carries these witnesses to every hyperplane in its orbit. The
large-subspace pointwise-fixer result makes the cubic action nontrivial.

No assertion about the square of the mover is made: the derived cyclic
normalizer permutes the three fixed hyperplanes cyclically. The source
component comparison can instead be made symmetrically in two hyperplanes.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815. The root conventions
are the imported licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes
open Subgroup
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "D" => commutator (Model F)

private def cubicMover : D := wordElement
  [false,true,true,false,false,true,false,true,false,false,true,true,false]

private theorem cubicMover_inverts :
    cubicMover * binaryB F * cubicMover⁻¹ = (binaryB F)⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply Atlas.SplitOctonion.linearMap_ext
  intro i
  funext j
  exact (by decide +kernel : ∀ i j,
    (cubicMover * binaryB F * cubicMover⁻¹).val.val
      (Atlas.SplitOctonion.basisVector i) j =
      ((binaryB F)⁻¹).val.val (Atlas.SplitOctonion.basisVector i) j) i j

private theorem cubicMover_moves : act cubicMover.val 0 ≠ 0 := by
  rw [cubicMover, act_word]
  decide +kernel

private theorem cancel_act (g : Model F) (a : Parameters) :
    act g⁻¹ (act g a) = a := by
  rw [← act_mul, inv_mul_cancel, act_one]

private theorem binaryB_order : orderOf (binaryB F) = 3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · calc
      (binaryB F) ^ 3 = binaryB F * (binaryB F * binaryB F) := by
        rw [pow_succ, pow_two, mul_assoc]
      _ = 1 := binaryB_cube F
  · intro he
    have hh := congrArg (fun g : D => act g.val (![1,0,0,0,0,0] : Parameters)) he
    rw [act_binaryB, Subgroup.coe_one, act_one] at hh
    exact (by decide +kernel :
      stepB (![1,0,0,0,0,0] : Parameters) ≠ ![1,0,0,0,0,0]) hh

/-- Every norm-zero hyperplane has a nontrivial derived cubic and a cyclic
normalizer element moving it. This is the literal seven-space version. -/
theorem norm_zero_cubic_mover (a : Parameters) (ha : normClass a = 0) :
    ∃ x l : D, orderOf x = 3 ∧
      (hyperplane a).map (traceZeroAction F x.val) = hyperplane a ∧
      (∃ v ∈ hyperplane a, traceZeroAction F x.val v ≠ v) ∧
      l * x * l⁻¹ = x⁻¹ ∧
      l ∈ normalizer (zpowers x : Set D) ∧
      (hyperplane a).map (traceZeroAction F l.val) ≠ hyperplane a := by
  obtain ⟨g, hg⟩ := exists_derived_seed a
  have hs : seed (normClass a) = 0 := by rw [ha]; decide +kernel
  have hg0 : act g.val 0 = a := hs ▸ hg
  let x : D := g * binaryB F * g⁻¹
  let l : D := g * cubicMover * g⁻¹
  have hxo : orderOf x = 3 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective (binaryB F)).trans binaryB_order
  have hxinv : l * x * l⁻¹ = x⁻¹ := by
    dsimp only [x, l]
    calc
      _ = g * (cubicMover * binaryB F * cubicMover⁻¹) * g⁻¹ := by group
      _ = g * (binaryB F)⁻¹ * g⁻¹ := by rw [cubicMover_inverts]
      _ = _ := by group
  have hgn : act g.val⁻¹ a = 0 := by
    conv_lhs => rw [← hg0]
    rw [← act_mul, inv_mul_cancel, act_one]
  have hxf : act x.val a = a := by
    have hB0 : stepB 0 = 0 := by decide +kernel
    dsimp only [x]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, act_mul, hgn, act_binaryB, hB0]
    exact hg0
  have hlm : act l.val a ≠ a := by
    intro he
    have hh := congrArg (fun p => act g.val⁻¹ p) he
    simp only [l, Subgroup.coe_mul, Subgroup.coe_inv, act_mul, hgn] at hh
    have hh' : act cubicMover.val 0 = 0 := by
      simpa only [cancel_act] using hh
    exact cubicMover_moves hh'
  refine ⟨x, l, hxo, ?_, ?_, hxinv, ?_, ?_⟩
  · rw [map_hyperplane, hxf]
  · by_contra! hfix
    have he := pointwise_large_subspace_trivial (hyperplane a)
      (by rw [finrank_hyperplane]; omega) (identity_not_mem a) x.val hfix
    have hx1 : x = 1 := Subtype.ext he
    rw [hx1, orderOf_one] at hxo
    norm_num at hxo
  · rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (l * x * l⁻¹) = zpowers x
    rw [hxinv, zpowers_inv]
  · rw [map_hyperplane]
    exact fun he => hlm (hyperplane_injective he)

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
