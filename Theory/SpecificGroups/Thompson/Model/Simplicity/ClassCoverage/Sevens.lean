module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Reduction
public import Mathlib.GroupTheory.Sylow

/-!
# Order-seven coverage in the Thompson matrix model

The ATLAS `ThG1-max11W1` program gives generators for a subgroup of the
normalizer of a Sylow seven-subgroup.  We retain the straight-line program as
a word definition and extract two commuting order-seven words from its two
outputs.  The matrix certificates for the order `49` and for the local fusion
are deliberately separate inputs to the assembly theorem below.

Source: <https://brauer.maths.qmul.ac.uk/Atlas/spor/Th/words/ThG1-max11W1>.
The source program is used only to choose words; all structural assertions
needed by the theorem are explicit Lean hypotheses.
-/

@[expose] public section

namespace Thompson.Simplicity

open PrimeCyclicCoverage

/- The literal `ThG1-max11W1` straight-line program. -/
def sevensProgram {G : Type*} [Group G] (a b : G) : G × G :=
  let r1 := a
  let r2 := b
  let r3 := r1 * r2
  let r4 := r3 * r2
  let r5 := r4 ^ 3
  let r1 := r5 * r4
  let r5 := r4 ^ 8
  let r6 := r5 * r4
  let r4 := r3 * r3
  let r7 := r5 * r4
  let r4 := r5 * r3
  let r3 := r4 * r4
  let r5 := r4 * r7
  let r4 := r3 * r6
  let r3 := r1 ^ 5
  let r6 := r5⁻¹
  let r7 := r2 * r5
  let r1 := r6 * r7
  let r6 := r4⁻¹
  let r7 := r3 * r4
  let r2 := r6 * r7
  (r1, r2)

/-- The two outputs of `ThG1-max11W1`. -/
def sevensU : Model := (sevensProgram generatorA generatorB).1

def sevensV : Model := (sevensProgram generatorA generatorB).2

/-- An order-seven word in the derived subgroup of the max11 program. -/
def sevensZ : Model := sevensU * sevensV ^ 2 * sevensU⁻¹ * sevensV ^ 2

/-- A second commuting order-seven word. -/
def sevensY : Model := sevensU * sevensZ * sevensU⁻¹

/-- The concrete candidate Sylow seven-subgroup. -/
def sevensSubgroup : Subgroup Model :=
  Subgroup.closure {sevensZ, sevensY}

/-- The two local cyclic representatives. -/
def sevensLocalRepresentative : Fin 2 → Model := ![sevensZ, sevensY]

theorem sevensZ_mem : sevensZ ∈ sevensSubgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem sevensY_mem : sevensY ∈ sevensSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The proposed order leaves no factor of `7` in the index of a subgroup of
order `49`. -/
theorem sevens_not_dvd_index (H : Subgroup Model)
    (hcard : Nat.card Model = 90745943887872000)
    (hH : Nat.card H = 49) :
    ¬7 ∣ H.index := by
  intro hd
  have he : 343 ∣ Nat.card Model := by
    rw [← H.card_mul_index, hH]
    exact Nat.mul_dvd_mul_left 49 hd
  rw [hcard] at he
  norm_num at he

/-- Local order-seven coverage transfers from the concrete subgroup once its
cardinality has been certified. -/
theorem sevens_coverage_of_card_49
    (hcard : Nat.card Model = 90745943887872000)
    {ι : Type*} (r : ι → Model)
    (P : Subgroup Model) (hP : Nat.card P = 49)
    (hlocal : ∀ y : Model, y ∈ P → orderOf y = 7 →
      ∃ i k g, r i = g * y ^ k * g⁻¹) :
    CoversPrime r 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : IsPGroup 7 P := IsPGroup.of_card (n := 2) hP
  exact prime_cyclic_coverage_of_sylow r
    (hp.toSylow (sevens_not_dvd_index P hcard hP)) hlocal

/-- Assemble the requested order-seven coverage from the two concrete local
cyclic classes and their fusion witnesses into representative `5`. -/
theorem covers_seven_of_local_certificates
    (hcard : Nat.card Model = 90745943887872000)
    (hP : Nat.card sevensSubgroup = 49)
    (hlocal : ∀ y : Model, y ∈ sevensSubgroup → orderOf y = 7 →
      ∃ i k g, sevensLocalRepresentative i = g * y ^ k * g⁻¹)
    (hfusion : ∀ i : Fin 2, ∃ k g,
      primeRepresentative 5 =
        g * sevensLocalRepresentative i ^ k * g⁻¹) :
    CoversPrime primeRepresentative 7 := by
  have hc : CoversPrime sevensLocalRepresentative 7 :=
    sevens_coverage_of_card_49 hcard sevensLocalRepresentative
      sevensSubgroup hP hlocal
  intro x hx
  obtain ⟨i, k, g, hi⟩ := hc x hx
  obtain ⟨l, h, hh⟩ := hfusion i
  refine ⟨5, k * l, h * g, ?_⟩
  rw [hi, conj_pow, ← pow_mul] at hh
  simpa only [mul_inv_rev, mul_assoc] using hh

end Thompson.Simplicity
