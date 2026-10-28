module

public import Theory.Representation.G2BinaryPlaneOrbits.Basic
public import Theory.Representation.G2BinaryPlaneOrbits.Certificate

/-!
# Uniqueness of the binary Sylow-invariant plane

Three explicit positive-root products belong to the actual derived Sylow
subgroup. Their off-diagonal actions are the three operators of `Certificate`.
A basis of any binary order-four subspace identifies its elements with zero,
the two basis vectors, and their sum. Invariance therefore supplies the finite
certificate hypotheses and forces the subspace into the literal marked plane.
Equality follows from the common cardinality four. No generation claim is used.

The root tuples also occur in `BinaryParabolicPair.WreathedSylow`; their
derived membership is proved directly through the existing long-root quotient.
Source: Aschbacher–Smith, printed p.1132 (PDF p.1149), C.1.30 and B.5.3–6.
Root conventions come from the attributed ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.BinaryPlane
open Atlas.G2.Explicit Atlas.G2.BinaryParabolicPair Atlas.SplitOctonion
open Representation.BinaryOffender SylowCoordinates

private def parameters (i : Fin 3) : Fin 6 → ZMod 2 :=
  ![![0,0,0,1,0,1], ![1,1,1,0,0,1], ![0,0,0,0,1,0]] i
private def operator (i : Fin 3) : Six → Six := ![stepS, stepT, stepZ] i

private theorem product_mem_derived (a : Fin 6 → ZMod 2) (ha : a 2 + a 3 + a 5 = 0) :
    unipotentProduct a ∈ commutator (Model (ZMod 2)) := by
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (unipotentProduct a) = 1
  simp only [unipotentProduct, map_mul, BinaryException.project_A,
    BinaryException.project_B, BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  rw [← map_mul, ← map_mul, rootF_add, rootF_add, ha, rootF_zero, map_one]

private def generator (i : Fin 3) : Actor :=
  ⟨unipotentProduct (parameters i), product_mem_derived _ (by fin_cases i <;> decide +kernel)⟩

private theorem generator_mem (i : Fin 3) : generator i ∈ standardSylow :=
  derivedSylow_eq.ge (unipotentProduct_mem _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem coordinate_formula : ∀ (i : Fin 3) (x : Carrier (ZMod 2)),
    trace x = 0 → binaryOffDiagonal (ZMod 2) ((unipotentProduct (parameters i)).val x) =
      operator i (binaryOffDiagonal (ZMod 2) x) := by decide +kernel

private theorem coordinates_action_mk (g : Actor) (x : TraceZero (ZMod 2)) :
    binaryCoordinates (ZMod 2) (action g (mk (ZMod 2) x)) =
      binaryOffDiagonal (ZMod 2) (g.val.val x.val) := rfl

private theorem coordinates_generator (i : Fin 3) (v : Coefficients) :
    binaryCoordinates (ZMod 2) (action (generator i) v) =
      operator i (binaryCoordinates (ZMod 2) v) := by
  obtain ⟨x,rfl⟩ := mk_surjective (ZMod 2) v
  rw [coordinates_action_mk]
  exact coordinate_formula i x.val x.property

/-- An order-four plane invariant under the actual standard Sylow is the
literal marked quotient plane. -/
theorem eq_standardPlane_of_standardSylow (W : Submodule (ZMod 2) Coefficients)
    (hW : Nat.card W = 4)
    (hS : (standardSylow : Subgroup Actor) ≤ subspaceStabilizer action W) :
    W = standardPlane := by
  have hdim : Module.finrank (ZMod 2) W = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    simpa [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] using hW
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hdim
  let x : Coefficients := (b 0).val
  let y : Coefficients := (b 1).val
  have hspan (w : W) : ∃ a c : ZMod 2, a • x + c • y = w.val := by
    refine ⟨b.repr w 0, b.repr w 1, ?_⟩
    have hb := b.sum_repr w
    rw [Fin.sum_univ_two] at hb
    exact congrArg (fun z : W => z.val) hb
  have hcases (w : W) : w.val = 0 ∨ w.val = x ∨ w.val = y ∨ w.val = x+y := by
    obtain ⟨a,c,he⟩ := hspan w
    have hb : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide +kernel
    rcases hb a with rfl | rfl <;> rcases hb c with rfl | rfl <;> simp_all
  have hpair (g : Actor) (hg : g ∈ standardSylow) (w : W) :
      inPair (binaryCoordinates (ZMod 2) x) (binaryCoordinates (ZMod 2) y)
        (binaryCoordinates (ZMod 2) (action g w.val)) := by
    have hw : action g w.val ∈ W := (hS hg w.val).mpr w.property
    rcases hcases ⟨_,hw⟩ with h | h | h | h
    all_goals
      change action g w.val = _ at h
      unfold inPair
      rw [h]
      simp
  have hx (i : Fin 3) : inPair (binaryCoordinates (ZMod 2) x)
      (binaryCoordinates (ZMod 2) y) (operator i (binaryCoordinates (ZMod 2) x)) := by
    rw [← coordinates_generator]
    exact hpair (generator i) (generator_mem i) (b 0)
  have hy (i : Fin 3) : inPair (binaryCoordinates (ZMod 2) x)
      (binaryCoordinates (ZMod 2) y) (operator i (binaryCoordinates (ZMod 2) y)) := by
    rw [← coordinates_generator]
    exact hpair (generator i) (generator_mem i) (b 1)
  have hc := certificate _ _ (hx 0) (hy 0) (hx 1) (hy 1) (hx 2) (hy 2)
  have hx0 : x ∈ standardPlane := (mem_standardPlane_iff x).mpr
    ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1⟩
  have hy0 : y ∈ standardPlane := (mem_standardPlane_iff y).mpr hc.2.2.2.2
  have hle : W ≤ standardPlane := by
    intro w hw
    obtain ⟨a,c,he⟩ := hspan ⟨w,hw⟩
    change a • x + c • y = w at he
    rw [← he]
    exact standardPlane.add_mem (standardPlane.smul_mem a hx0) (standardPlane.smul_mem c hy0)
  let : Finite standardPlane.toAddSubgroup :=
    Finite.of_equiv (ZMod 2 × ZMod 2) standardPlaneEquiv.symm
  have he : W.toAddSubgroup = standardPlane.toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hle (by change Nat.card standardPlane ≤ Nat.card W; rw [hW,card_standardPlane])
  ext w
  exact SetLike.ext_iff.mp he w
end Atlas.G2.Natural.BinaryPlane
