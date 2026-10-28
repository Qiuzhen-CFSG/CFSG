module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Setup
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.Coordinates
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Local inputs for the exceptional quotient

`ExceptionalLocalStructure` records the homocyclic subgroup and coset fusion
constructed in the first paragraph of GLS 4, Chapter 2, Lemma 15.7.
Its kernel is the literal `[⟨Jᴹ⟩, D ∩ L]`, internal to `M`, and its
involutions are exactly the distinguished closure `M°`. These are explicit
intermediate conclusions, not additional assumptions of the source theorem.
Their construction is still required by the final source assembly.

The lemmas below derive the order-two quotient kernel and translate fusion
of `R ∖ R₀` into fusion of the literal quotient fiber used by the square
lifting argument. `M° ≤ R₀` also justifies the source's barred notation:
the third isomorphism theorem gives `(M/M°)/(R₀/M°) ≃ M/R₀`.

`ExceptionalFieldAction` is an actual faithful doubly transitive action of
`M/O₂(M)` on GF(2ⁿ), with scalar and semilinear stabilizer coordinates.
It contains no classification conclusion. The action must be constructed
from the source coset action before applying the classification theorem.
-/

public section

namespace BenderSuzuki.ZD
open Subgroup

/-- The precise local subgroup and fusion data, before action classification.
An inhabitant must be constructed from the original linear-case hypotheses. -/
structure ExceptionalLocalStructure {G : Type*} [Group G]
    (Z : Set G) (M : Subgroup G) (z t : G) (n : ℕ) where
  kernel : Subgroup M
  kernel_normal : kernel.Normal
  kernel_eq : kernel = ⁅linearCentralizerClosure M z t,
    (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M⁆
  homocyclic : kernel ≃* Multiplicative (Fin n → ZMod 4)
  distinguished_le : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ kernel
  omega : ∀ x : kernel, x ^ 2 = 1 ↔
    (x : M) ∈ (closure (Z ∩ (M : Set G))).subgroupOf M
  u : M
  u_mem : (u : G) ∈ centralizer (residualGenerated M z t : Set G)
  u_ne_one : (u : G) ≠ 1
  u_not_mem : u ∉ kernel
  fusion : ∀ v : M, v ∈ linearCentralizerClosure M z t → v ∉ kernel →
    IsConj (v : G) (u : G)

attribute [instance] ExceptionalLocalStructure.kernel_normal

namespace ExceptionalLocalStructure
variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G} {z t : G} {n : ℕ}
    (d : ExceptionalLocalStructure Z M z t n)

/-- The commutator definition places the kernel inside the normal closure. -/
theorem kernel_le_closure : d.kernel ≤ linearCentralizerClosure M z t := by
  let : (linearCentralizerClosure M z t).Normal := by
    unfold linearCentralizerClosure
    infer_instance
  rw [d.kernel_eq]
  exact commutator_le_left _ _

/-- The actual homocyclic coordinates give the source order `q²`. -/
theorem kernel_card : Nat.card d.kernel = (2 ^ n) ^ 2 := by
  calc
    Nat.card d.kernel = Nat.card (Multiplicative (Fin n → ZMod 4)) :=
      Nat.card_congr d.homocyclic.toEquiv
    _ = 4 ^ n := by simp
    _ = (2 ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num

/-- The specified centralizer element lies in its normal closure. -/
theorem u_mem_closure : d.u ∈ linearCentralizerClosure M z t :=
  Subgroup.subset_normalClosure d.u_mem

/-- In the equality branch the literal image `V/R₀` has order two. -/
theorem core_image_card_two [Finite G]
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hRV : linearCentralizerClosure M z t = pCore 2 M) :
    Nat.card ((pCore 2 M).map (QuotientGroup.mk' d.kernel)) = 2 := by
  have hle : d.kernel ≤ pCore 2 M := d.kernel_le_closure.trans hRV.le
  have hc := (d.kernel.subgroupOf (pCore 2 M)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hc
  change Nat.card d.kernel * d.kernel.relIndex (pCore 2 M) = Nat.card (pCore 2 M) at hc
  have hi := (pCore 2 M).relIndex_ker (QuotientGroup.mk' d.kernel)
  rw [QuotientGroup.ker_mk'] at hi
  have hV : Nat.card (pCore 2 M) = 2 * (2 ^ n) ^ 2 := hRV ▸ hR
  rw [hi, d.kernel_card, hV] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2 ^ n) ^ 2)
    (hc.trans (Nat.mul_comm _ _))

/-- The source fusion statement applies to every lift of the marked class. -/
theorem marked_coset_fusion (v : M)
    (hv : QuotientGroup.mk' d.kernel v = QuotientGroup.mk' d.kernel d.u) :
    IsConj (v : G) (d.u : G) := by
  have hdiv : v / d.u ∈ d.kernel := QuotientGroup.eq_iff_div_mem.mp hv
  apply d.fusion v
  · simpa using (linearCentralizerClosure M z t).mul_mem
      (d.kernel_le_closure hdiv) d.u_mem_closure
  · intro hvK
    apply d.u_not_mem
    simpa [div_eq_mul_inv, mul_assoc] using d.kernel.mul_mem (d.kernel.inv_mem hdiv) hvK

end ExceptionalLocalStructure

/-- The faithful field coordinates required by the independent action theorem. -/
structure ExceptionalFieldAction {G : Type*} [Group G] (M : Subgroup G) (n : ℕ) where
  action : MulAction (M ⧸ pCore 2 M) (GaloisField 2 n)
  faithful : letI := action; FaithfulSMul (M ⧸ pCore 2 M) (GaloisField 2 n)
  two_transitive : letI := action;
    MulAction.IsMultiplyPretransitive (M ⧸ pCore 2 M) (GaloisField 2 n) 2
  coordinates : letI := action;
    MulAction.SemilinearPointStabilizer.Coordinates (M ⧸ pCore 2 M) (GaloisField 2 n)

end BenderSuzuki.ZD
