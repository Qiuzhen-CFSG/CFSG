module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.FactorMaps

/-!
# The exact two-factor exceptional twist

The Weyl word interchanges the marked long and short A₂ factors; the long
factor changes sign and the short factor squares its root parameters.
Opposition supplies the parity correction. Checking the four elementary
SL₃ curves extends these equations to the full factors and proves the exact
`SL3Pair.pairTwist` identity, including its inverse-transpose convention.
A faithful short-root chart consequently produces all of `SubsystemData`.
Source: GLS3 Example 2.6.3 and Table 4.7.3A.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
open ReeF4.WordRelations
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {F : Type*} [Field F] [CharP F 2]

theorem graph_simpleGenerator (s k : Bool) (t : F) :
    graph (simpleGenerator s k t) = simpleGenerator (!s) k t := by
  change (Matrix.SpecialLinearGroup.transpose (simpleGenerator s k t))⁻¹ = _
  have ht : Matrix.SpecialLinearGroup.transpose (simpleGenerator s k t) =
      simpleGenerator (!s) k t := by
    cases s <;> cases k <;> apply Subtype.ext
    all_goals
      ext i j
      fin_cases i <;> fin_cases j <;> simp [simpleGenerator, modelGenerator,
        Matrix.SpecialLinearGroup.transvection_coe]
  rw [ht]
  cases s <;> cases k <;>
    simp [simpleGenerator, modelGenerator, Matrix.SpecialLinearGroup.transvection_inv,
      CharTwo.neg_eq]

theorem field_pow_simpleGenerator (n : ℕ) (s k : Bool) (t : F) :
    (field ^ n) (simpleGenerator s k t) = simpleGenerator s k (t ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change field ((field ^ n) (simpleGenerator s k t)) = _
    rw [ih]
    change Matrix.SpecialLinearGroup.map (frobenius F 2) _ = _
    rw [map_simpleGenerator, frobenius_def, ← pow_mul, ← pow_succ]

theorem graph_signedFrobenius_pow (m : ℕ) :
    graph (F := F) * signedFrobenius ^ m = graph ^ m * graph * field ^ m := by
  rw [signedFrobenius, graph_field.mul_pow, ← mul_assoc, ← pow_succ', pow_succ]

theorem signedFrobenius_succ_graph (m : ℕ) :
    signedFrobenius (F := F) ^ (m + 1) * graph = graph ^ m * field ^ (m + 1) := by
  rw [signedFrobenius, graph_field.mul_pow]
  calc
    (graph ^ (m + 1) * field ^ (m + 1)) * graph =
        (graph ^ (m + 1) * graph) * field ^ (m + 1) := by
      rw [mul_assoc, ← (graph_field.pow_right (m + 1)).eq, ← mul_assoc]
    _ = graph ^ m * field ^ (m + 1) := by
      rw [pow_succ, mul_assoc (graph ^ m) graph graph, ← pow_two, graph_sq, mul_one]

variable [IsAlgClosed F]

theorem markedMap_opposition {f : SL3 F →* AlgebraicPoints F}
    {r : Bool → F4Chevalley.Root} (hf : MarkedMap f r) (A : SL3 F) :
    opposition * f A * opposition⁻¹ = f (graph A) := by
  have he : (MulAut.conj (opposition (F := F))).toMonoidHom.comp f = f.comp graph := by
    apply hom_ext_simple
    intro s k t
    change opposition * f (simpleGenerator s k t) * opposition⁻¹ =
      f (graph (simpleGenerator s k t))
    rw [hf, graph_simpleGenerator, hf, opposition_root]
    congr 1
    cases s <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, neg_neg]
  exact DFunLike.congr_fun he A

theorem markedMap_opposition_pow {f : SL3 F →* AlgebraicPoints F}
    {r : Bool → F4Chevalley.Root} (hf : MarkedMap f r) (n : ℕ) (A : SL3 F) :
    opposition ^ n * f A * (opposition ^ n)⁻¹ = f ((graph ^ n) A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ' (graph (F := F))]
    change (opposition * opposition ^ n) * f A * (opposition * opposition ^ n)⁻¹ =
      f (graph ((graph ^ n) A))
    rw [mul_inv_rev]
    calc
      (opposition * opposition ^ n) * f A * ((opposition ^ n)⁻¹ * opposition⁻¹) =
          opposition * (opposition ^ n * f A * (opposition ^ n)⁻¹) * opposition⁻¹ := by
        simp only [mul_assoc]
      _ = _ := by rw [ih, markedMap_opposition hf]

theorem reeTwist_long_root (m : ℕ) (s k : Bool) (t : F) :
    wordElement twistWord * (algebraicReeTwist m).onPoints
        (rootPoint (signedRoot s (longRoot k)) t) * (wordElement twistWord)⁻¹ =
      rootPoint (signedRoot (!s) (shortRoot k)) (t ^ (2 ^ m)) := by
  rw [algebraicReeTwist_rootAction, if_pos (signed_long s k), wordElement_root]
  congr 1
  cases s <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
    Bool.not_false, Bool.not_true, exceptionalRootPermutation_neg, rootWord_neg,
    twist_long_target, neg_neg]

theorem reeTwist_short_root (m : ℕ) (s k : Bool) (t : F) :
    wordElement twistWord * (algebraicReeTwist m).onPoints
        (rootPoint (signedRoot s (shortRoot k)) t) * (wordElement twistWord)⁻¹ =
      rootPoint (signedRoot s (longRoot k)) (t ^ (2 ^ (m + 1))) := by
  rw [algebraicReeTwist_rootAction, if_neg (signed_short s k), wordElement_root]
  congr 1
  cases s <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
    exceptionalRootPermutation_neg, rootWord_neg, twist_short_target]


/-- Opposition corrects the parity of the signed Frobenius parameter. -/
def correctedWeyl (m : ℕ) : AlgebraicPoints F := opposition ^ m * wordElement twistWord

omit [CharP F 2] in
theorem correctedWeyl_conjugate (m : ℕ) (x : AlgebraicPoints F) :
    correctedWeyl m * x * (correctedWeyl m)⁻¹ =
      opposition ^ m * (wordElement twistWord * x * (wordElement twistWord)⁻¹) *
        (opposition ^ m)⁻¹ := by
  simp only [correctedWeyl, mul_inv_rev, mul_assoc]

theorem marked_pair_long {L S : SL3 F →* AlgebraicPoints F}
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot) (m : ℕ) (A : SL3 F) :
    correctedWeyl m * (algebraicReeTwist m).onPoints (L A) * (correctedWeyl m)⁻¹ =
      S (graph ((signedFrobenius ^ m) A)) := by
  have he : ((MulAut.conj (correctedWeyl (F := F) m)).toMonoidHom.comp
      (algebraicReeTwist m).onPoints).comp L = S.comp (graph * signedFrobenius ^ m) := by
    apply hom_ext_simple
    intro s k t
    change correctedWeyl m * (algebraicReeTwist m).onPoints (L (simpleGenerator s k t)) *
      (correctedWeyl m)⁻¹ = S ((graph * signedFrobenius ^ m : Monoid.End (SL3 F)) (simpleGenerator s k t))
    rw [correctedWeyl_conjugate, hL, reeTwist_long_root, ← hS,
      markedMap_opposition_pow hS, ← graph_simpleGenerator, ← field_pow_simpleGenerator,
      graph_signedFrobenius_pow]
    rfl
  exact DFunLike.congr_fun he A

theorem marked_pair_short {L S : SL3 F →* AlgebraicPoints F}
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot) (m : ℕ) (A : SL3 F) :
    correctedWeyl m * (algebraicReeTwist m).onPoints (S A) * (correctedWeyl m)⁻¹ =
      L ((signedFrobenius ^ (m + 1)) (graph A)) := by
  have he : ((MulAut.conj (correctedWeyl (F := F) m)).toMonoidHom.comp
      (algebraicReeTwist m).onPoints).comp S =
      L.comp (signedFrobenius ^ (m + 1) * graph) := by
    apply hom_ext_simple
    intro s k t
    change correctedWeyl m * (algebraicReeTwist m).onPoints (S (simpleGenerator s k t)) *
      (correctedWeyl m)⁻¹ = L ((signedFrobenius ^ (m + 1) * graph : Monoid.End (SL3 F)) (simpleGenerator s k t))
    rw [correctedWeyl_conjugate, hS, reeTwist_short_root, ← hL,
      markedMap_opposition_pow hL, ← field_pow_simpleGenerator, signedFrobenius_succ_graph]
    rfl
  exact DFunLike.congr_fun he A

/-- The literal Ree twist agrees with the source two-factor convention. -/
theorem pairMap_intertwines (L S : SL3 F →* AlgebraicPoints F)
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot) (m : ℕ)
    (x : SL3 F × SL3 F) :
    correctedWeyl m * (algebraicReeTwist m).onPoints (pairMap L S hL hS x) *
      (correctedWeyl m)⁻¹ = pairMap L S hL hS (pairTwist m x) := by
  rcases x with ⟨A, B⟩
  change correctedWeyl m * (algebraicReeTwist m).onPoints (L A * S B) *
      (correctedWeyl m)⁻¹ =
    L ((signedFrobenius ^ (m + 1)) (graph B)) * S (graph ((signedFrobenius ^ m) A))
  calc
    _ = (correctedWeyl m * (algebraicReeTwist m).onPoints (L A) * (correctedWeyl m)⁻¹) *
        (correctedWeyl m * (algebraicReeTwist m).onPoints (S B) * (correctedWeyl m)⁻¹) := by
      rw [map_mul]
      group
    _ = _ := by
      rw [marked_pair_long hL hS, marked_pair_short hL hS]
      exact (markedMaps_commute hL hS _ _).eq.symm

/-- A faithful short chart supplies the complete split subsystem contract. -/
def dataOfShortMap (S : SL3 F →* AlgebraicPoints F) (hS : MarkedMap S shortRoot)
    (hi : Function.Injective S) (m : ℕ) : SubsystemData m F where
  map := pairMap (longMap S) S (longMap_marked hS) hS
  kernel := pairMap_kernel _ _ (longMap_marked hS) hS (longMap_injective S hi) hi
  weyl := correctedWeyl m
  intertwines := pairMap_intertwines _ _ (longMap_marked hS) hS m

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
