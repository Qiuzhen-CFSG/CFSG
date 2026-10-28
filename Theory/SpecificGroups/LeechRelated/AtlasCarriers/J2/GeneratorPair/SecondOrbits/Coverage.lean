module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.NormalForms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.Coverage.Transitions

/-!
# Coverage by the four J₂ transversals

Every element of the concrete ATLAS carrier is a word in the first signed
alphabet: its inverse indices are checked, and its first two letters equal
the retained generators. Word induction through the certified Schreier
transitions successively extracts the four transversal representatives.
The terminal residual is trivial, giving the published normal form in the
order `rep0 * rep1 * rep2 * rep3`.

Source: the retained ATLAS `J2G1-p100B0` permutations and the witnesses in
`SecondOrbits/source/witnesses.json`, documented by its adjacent README.
This proof uses no order, simplicity, or exact-stabilizer assertion.
-/

namespace Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open Theory.GroupTheory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

private theorem word_decompose {G : Type*} [Group G] {n m p : Nat}
    (gen : Fin n → G) (next : Fin p → G) (rep : Fin m → G)
    (base : Fin m) (hbase : rep base = 1)
    (hstep : ∀ g r, ∃ s w, gen g * rep r = rep s * evalWord next w)
    (w : List (Fin n)) : ∃ r v, evalWord gen w = rep r * evalWord next v := by
  induction w with
  | nil => exact ⟨base, [], by simp only [evalWord, hbase, mul_one]⟩
  | cons g w ih =>
    obtain ⟨r, v, hv⟩ := ih
    obtain ⟨s, u, hu⟩ := hstep g r
    refine ⟨s, u ++ v, ?_⟩
    simp only [evalWord, hv, evalWord_append]
    rw [← mul_assoc, hu, mul_assoc]

private theorem inverse0 : ∀ i, gen0 (inv0 i) = (gen0 i)⁻¹ := by
  have h : ∀ i x, gen0Map (inv0 i) x = gen0InvMap i x := by
    apply allFin
    decide +kernel
  intro i
  exact Equiv.ext (h i)

private theorem carrier_word (y : Carrier) : ∃ w, inclusion y = evalWord gen0 w := by
  let H := wordSubgroup gen0 inv0 inverse0
  have ha : gen0 0 = generatorA := by
    rw [generatorA_eq_table]
    apply Equiv.ext
    decide +kernel
  have hb : gen0 1 = generatorB := by
    rw [generatorB_eq_table]
    apply Equiv.ext
    decide +kernel
  have hle : Subgroup.closure
      ({generatorA, generatorB} : Set (Equiv.Perm (Fin 100))) ≤ H := by
    apply (Subgroup.closure_le H).2
    intro z hz
    rcases hz with hz | hz
    · subst z
      exact ⟨[0], by simpa only [evalWord, mul_one] using ha⟩
    · have hz' : z = generatorB := hz
      subst z
      exact ⟨[1], by simpa only [evalWord, mul_one] using hb⟩
  obtain ⟨w, hw⟩ := hle y.property
  exact ⟨w, hw.symm⟩

private theorem rep0_zero : rep0 0 = 1 := by
  apply Equiv.ext
  decide +kernel

private theorem rep1_zero : rep1 0 = 1 := by
  apply Equiv.ext
  decide +kernel

private theorem rep2_zero : rep2 0 = 1 := by
  apply Equiv.ext
  decide +kernel

private theorem rep3_zero : rep3 0 = 1 := by
  apply Equiv.ext
  decide +kernel

private theorem terminal_word (w : List (Fin 2)) : ∃ r, evalWord gen3 w = rep3 r := by
  induction w with
  | nil => exact ⟨0, rep3_zero.symm⟩
  | cons g w ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨s, hs⟩ := transition3 g r
    exact ⟨s, by simpa only [evalWord, hr] using hs⟩

/-- The four published transversals cover the actual ATLAS-generated carrier. -/
public theorem normalForm_cover (y : Carrier) : ∃ i : Index, inclusion y = normalForm i := by
  obtain ⟨w0, h0⟩ := carrier_word y
  obtain ⟨r0, w1, h1⟩ := word_decompose gen0 gen1 rep0 0 rep0_zero transition0 w0
  obtain ⟨r1, w2, h2⟩ := word_decompose gen1 gen2 rep1 0 rep1_zero transition1 w1
  obtain ⟨r2, w3, h3⟩ := word_decompose gen2 gen3 rep2 0 rep2_zero transition2 w2
  obtain ⟨r3, h4⟩ := terminal_word w3
  refine ⟨(r0, r1, r2, r3), ?_⟩
  simp only [h0, h1, h2, h3, h4, normalForm, mul_assoc]

end Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
