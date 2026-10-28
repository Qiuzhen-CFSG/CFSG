module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixFourSupport

/-!
# The positive-parameter derived contribution in source (6.4)

For a positive Suzuki parameter, the ambient Omega of a shifted Suzuki root is
contained in the derived subgroup of the actual radical whenever that shifted
root is itself a root of the radical.  This is transported from the literal
simple-root identity `[U,U] = Phi(U) = Omega₁(U)`; it uses the same right
conjugation as `rootAt` and does not identify either field.

Applying this to the support obtained in the preceding (6.4) product step
shows that the remaining linear factor already lies in the actual derived
radical.  This is the exact factor-membership input for the source argument
that removes that factor.  The final vanishing of the factor still requires
the centralizer case analysis on printed pp.52--54.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include μ hB in
/-- A positive Suzuki Omega contribution belongs to the radical derived group
whenever the shifted root is contained in that radical. -/
theorem source_positive_omega_le_derived
    (hmpos : 0 < m) (w : Weyl Q)
    (hA : rootAt Q split i w ≤ simpleRemainder Q split i) :
    omegaOneAmbient (rootAt Q split i w) ≤
      ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
  let n := representative w
  let e := (MulAut.conj (n : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split i).map e.toMonoidHom = rootAt Q split i w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']
    rfl
  have hΩ : (omegaOneAmbient (simpleRoot Q split i)).map e.toMonoidHom =
      omegaOneAmbient (rootAt Q split i w) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he]
  rw [← hΩ]
  have hcomm : _root_.commutator (simpleRoot Q split i) =
      frattini (simpleRoot Q split i) :=
    suzuki_derived_eq_frattini Q split i m μ hB hmpos
  have hfr : frattini (simpleRoot Q split i) =
      (omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i) :=
    suzuki_frattini_eq_omega Q split i m μ hB
  have hmap : ((omegaOneAmbient (simpleRoot Q split i)).subgroupOf
      (simpleRoot Q split i)).map (simpleRoot Q split i).subtype =
      omegaOneAmbient (simpleRoot Q split i) := by
    rw [map_subgroupOf_eq_of_le (omegaOneAmbient_le _)]
  have hle : omegaOneAmbient (simpleRoot Q split i) ≤
      (commutator (simpleRoot Q split i)).map (simpleRoot Q split i).subtype := by
    rw [← hmap,← hfr,← hcomm,map_subtype_commutator]
  have hle' : omegaOneAmbient (simpleRoot Q split i) ≤
      ⁅simpleRoot Q split i,simpleRoot Q split i⁆ := by
    simpa only [map_subtype_commutator] using hle
  have hcommle :
      (⁅simpleRoot Q split i,simpleRoot Q split i⁆).map e.toMonoidHom ≤
        ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
    rw [map_commutator,he]
    exact commutator_mono hA hA
  exact (map_mono hle').trans hcommle

private theorem source_six_four_simple_square (k : Fin 2) :
    Q.simple k * Q.simple k = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2

private theorem source_six_four_short_lengths (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i) = 3 := by
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega))
    (wordLength_alternatingWord Q b (n := 3) (by omega)))
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using hh false
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using hh true
  · exact (hij rfl).elim

/-- The two-step Suzuki root in the octagon is contained in the same endpoint
remainder.  This is the geometric root placement needed by the positive
factor step; no source commutator relation is used. -/
theorem source_six_four_shifted_root_le_remainder
    (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i) ≤ simpleRemainder Q split i := by
  have hi := source_six_four_short_lengths Q hm i j hij
  have hj := source_six_four_short_lengths Q hm j i hij.symm
  have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k :=
    inv_eq_of_mul_eq_one_right (source_six_four_simple_square Q k)
  apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i)
  · simp only [mul_inv_rev, hs]
    rw [hi.2.2, hi.2.1]
  · simp only [mul_inv_rev, hs, ← mul_assoc, source_six_four_simple_square,
      one_mul]
    rw [hj.2.1, hj.1]

include μ hB ν hC in
/-- In the positive Suzuki case, the linear factor in the preceding (6.4)
support decomposition is itself in the actual derived radical. -/
theorem source_six_four_positive_factor
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤
      pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)
    (hmpos : 0 < m)
    (z : X ⧸ Q.D)
    (hzD : z ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆)
    (hz : z ∈ ⁅simpleRoot Q split i,
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆) :
    ∃ a ∈ omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)),
      ∃ b ∈ rootAt Q split j (Q.simple i),
        b ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ ∧
        a*b = z := by
  obtain ⟨_,hp⟩ := source_six_four_product Q split i j m μ hB ν T hC hc hm hij hsize z hz
  obtain ⟨a,ha,b,hb,hab⟩ := hp
  have haD : a ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :=
    source_positive_omega_le_derived Q split i m μ hB hmpos
      (Q.simple j*Q.simple i)
      (source_six_four_shifted_root_le_remainder Q split i j hm hij) ha
  have hbD : b ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
    have hh := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
      Subgroup (X ⧸ Q.D)).mul_mem
      ((⁅simpleRemainder Q split i,simpleRemainder Q split i⁆).inv_mem haD) hzD
    rw [← hab,inv_mul_cancel_left] at hh
    exact hh
  exact ⟨a,ha,b,hb,hbD,hab⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
