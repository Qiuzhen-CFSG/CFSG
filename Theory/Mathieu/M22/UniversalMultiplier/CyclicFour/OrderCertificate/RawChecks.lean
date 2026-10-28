module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.OrderCertificate.Lifts

/-!
# Degree-4928 obligations for the lifted Schreier chain

The native degree-22 identities are already proved. Thus a transition in the
paired model needs only its first-coordinate identity. The fixed correction
exponents below were discovered by the untrusted script in `source/` and do not
assert their correctness. `step0_of_raw`–`step3_of_raw` and `terminal_of_raw`
connect exactly these remaining numerical obligations to the paired group.

Source: the native M₂₂ Schreier certificate and the literal ATLAS generators;
this is the finite-certificate input to the I.1.3(4) cover construction.
-/

namespace Sporadic.Mathieu.M22CyclicFour.OrderCertificate
open Theory.GroupTheory

@[expose] public section

/-- The first coordinate of the literal paired group. -/
noncomputable def firstProjection : Model →* Equiv.Perm (Fin 4928) :=
  (MonoidHom.fst _ _).comp Model.subtype

theorem firstProjection_generatorA : firstProjection generatorA = Data.aPerm := rfl

theorem firstProjection_generatorB : firstProjection generatorB = Data.bPerm := rfl

theorem model_ext {x y : Model}
    (hfirst : firstProjection x = firstProjection y)
    (hnative : ambientProjection x = ambientProjection y) : x = y :=
  Subtype.ext (Prod.ext hfirst hnative)

theorem native_centralWord : ambientProjection centralWord = 1 := by
  have h : projection centralWord = 1 := centralWord_mem_kernel
  calc
    ambientProjection centralWord = M22.subtype (projection centralWord) := rfl
    _ = M22.subtype 1 := congrArg M22.subtype h
    _ = 1 := M22.subtype.map_one

/-- Discovered exponents; the following predicate still requires their proof. -/
def correction0 : Fin 4 → Fin 22 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]]

/-- The remaining full-degree permutation identities at level 0. -/
def RawStep0 : Prop := ∀ i r,
  firstProjection (gen0 i) * firstProjection (rep0 r) =
    firstProjection (rep0 (m22L0Act i r)) *
      evalWord (fun j => firstProjection (gen1 j)) (m22L0Factor i r) *
        firstProjection centralWord ^ (correction0 i r).val

theorem step0_of_raw (h : RawStep0) : Step0 := by
  intro i r
  refine ⟨correction0 i r, model_ext ?_ ?_⟩
  · simpa only [map_mul, map_pow, map_evalWord] using h i r
  · simpa only [map_mul, map_pow, map_evalWord, projection_gen0,
      projection_rep0, projection_gen1, native_centralWord, one_pow, mul_one]
      using m22L0Step i r

/-- Discovered exponents; the following predicate still requires their proof. -/
def correction1 : Fin 6 → Fin 21 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 3, 0, 1, 0, 3, 0, 0, 0, 3, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 3, 1, 2, 2, 2, 0, 3, 3],
    ![0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 3, 0, 1, 0, 3, 0, 0, 0, 3, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 3, 3, 3, 3, 2, 0, 2, 0, 0, 0, 2, 1, 1, 2, 0, 1]]

/-- The remaining full-degree permutation identities at level 1. -/
def RawStep1 : Prop := ∀ i r,
  firstProjection (gen1 i) * firstProjection (rep1 r) =
    firstProjection (rep1 (m22L1Act i r)) *
      evalWord (fun j => firstProjection (gen2 j)) (m22L1Factor i r) *
        firstProjection centralWord ^ (correction1 i r).val

theorem step1_of_raw (h : RawStep1) : Step1 := by
  intro i r
  refine ⟨correction1 i r, model_ext ?_ ?_⟩
  · simpa only [map_mul, map_pow, map_evalWord] using h i r
  · simpa only [map_mul, map_pow, map_evalWord, projection_gen1,
      projection_rep1, projection_gen2, native_centralWord, one_pow, mul_one]
      using m22L1Step i r

/-- Discovered exponents; the following predicate still requires their proof. -/
def correction2 : Fin 8 → Fin 20 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 2, 0, 3, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 2, 2],
    ![0, 0, 0, 1, 0, 1, 3, 1, 1, 0, 2, 0, 2, 2, 3, 1, 3, 0, 2, 0],
    ![0, 0, 0, 1, 3, 3, 0, 0, 0, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2],
    ![0, 2, 0, 0, 1, 0, 3, 1, 2, 3, 1, 0, 0, 2, 0, 0, 0, 2, 2, 1],
    ![0, 0, 0, 0, 0, 2, 0, 3, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 2, 2],
    ![0, 3, 0, 0, 3, 0, 3, 2, 0, 3, 2, 0, 1, 3, 2, 1, 0, 2, 1, 0],
    ![0, 0, 0, 0, 0, 2, 3, 3, 2, 0, 1, 0, 3, 1, 3, 1, 2, 2, 2, 3],
    ![0, 1, 0, 3, 0, 0, 0, 2, 3, 2, 2, 0, 3, 3, 3, 0, 2, 2, 2, 0]]

/-- The remaining full-degree permutation identities at level 2. -/
def RawStep2 : Prop := ∀ i r,
  firstProjection (gen2 i) * firstProjection (rep2 r) =
    firstProjection (rep2 (m22L2Act i r)) *
      evalWord (fun j => firstProjection (gen3 j)) (m22L2Factor i r) *
        firstProjection centralWord ^ (correction2 i r).val

theorem step2_of_raw (h : RawStep2) : Step2 := by
  intro i r
  refine ⟨correction2 i r, model_ext ?_ ?_⟩
  · simpa only [map_mul, map_pow, map_evalWord] using h i r
  · simpa only [map_mul, map_pow, map_evalWord, projection_gen2,
      projection_rep2, projection_gen3, native_centralWord, one_pow, mul_one]
      using m22L2Step i r

/-- Discovered exponents; the following predicate still requires their proof. -/
def correction3 : Fin 6 → Fin 16 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 2, 2, 0, 0, 2, 2, 2, 2, 0, 2, 0],
    ![0, 0, 3, 1, 3, 0, 1, 2, 2, 0, 2, 2, 1, 3, 1, 3],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 2, 0, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0, 2],
    ![0, 2, 0, 0, 2, 3, 2, 1, 3, 1, 2, 0, 1, 1, 3, 3]]

/-- The remaining full-degree permutation identities at level 3. -/
def RawStep3 : Prop := ∀ i r,
  firstProjection (gen3 i) * firstProjection (rep3 r) =
    firstProjection (rep3 (m22L3Act i r)) *
      evalWord (fun j => firstProjection (gen4 j)) (m22L3Factor i r) *
        firstProjection centralWord ^ (correction3 i r).val

theorem step3_of_raw (h : RawStep3) : Step3 := by
  intro i r
  refine ⟨correction3 i r, model_ext ?_ ?_⟩
  · simpa only [map_mul, map_pow, map_evalWord] using h i r
  · simpa only [map_mul, map_pow, map_evalWord, projection_gen3,
      projection_rep3, projection_gen4, native_centralWord, one_pow, mul_one]
      using m22L3Step i r

/-- The last cubic identity in the degree-4928 action. -/
def RawTerminal : Prop := firstProjection (gen4 0) ^ 3 = firstProjection centralWord

theorem terminal_of_raw (h : RawTerminal) : Terminal := by
  apply model_ext
  · rw [map_pow]
    exact h
  · rw [map_pow, projection_gen4, native_centralWord]
    decide +kernel

end
end Sporadic.Mathieu.M22CyclicFour.OrderCertificate
