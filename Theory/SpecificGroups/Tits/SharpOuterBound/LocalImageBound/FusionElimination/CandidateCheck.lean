module
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.FusionElimination.Checks
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.PairCandidates

/-!
# Checking the mask against the two certified fusion labels

The two candidate tables are checked separately against `candidatePair`.
A monoid homomorphism transfers the fixed permutation words to point functions.
The kernel checks the resulting labels in rows of 64 candidates, keeping
memory bounded. Equality of both pairs of labels forces the published mask bit.

Source: Parrott (1972), §5, p.683; `LocalImageBound/TwoGenerators`.
The finite data are reproduced by `source/generate_certificate.py`.
-/

namespace Tits.SharpOuterBound.LocalImageBound.FusionElimination

def firstCandidatesData : Nat := 3539902257799392674533881783905627374121901605082917368119712297310529573053966182622547837411748890722419182506025722071113215976302484254867595367724697779488638418390424047481906977605015828349671731344172300970847584356802642873115082343652344238252986369587837619631807222113091267330138893561894389891187973444711636030956104377255927672511621188023378598361667754286690469938508260777571241756335773527362656003960836

def secondCandidatesData : Nat := 83627500110341734806851567819077451096838162087722338112933613339816259799027529183257932371174928930866781191843953162711169117845332224043014712608418184611682956473719442664568029496384735166143554600680064000

public def fastCandidatePair (i : Fin 8192) : Fin 2048 × Fin 2048 :=
  (⟨(firstCandidatesData >>> (11 * (i.val / 64))) % 2048, Nat.mod_lt _ (by decide)⟩,
   ⟨(secondCandidatesData >>> (11 * (i.val % 64))) % 2048, Nat.mod_lt _ (by decide)⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem firstCandidatesData_eq (j : Fin 128) :
    (⟨(firstCandidatesData >>> (11 * j.val)) % 2048, Nat.mod_lt _ (by decide)⟩ : Fin 2048) =
      firstIndices j := by
  revert j
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem secondCandidatesData_eq (j : Fin 64) :
    (⟨(secondCandidatesData >>> (11 * j.val)) % 2048, Nat.mod_lt _ (by decide)⟩ : Fin 2048) =
      secondIndices j := by
  revert j
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

public theorem fastCandidatePair_eq (i : Fin 8192) : fastCandidatePair i = candidatePair i :=
  Prod.ext (firstCandidatesData_eq ⟨i.val / 64, by omega⟩)
    (secondCandidatesData_eq ⟨i.val % 64, by omega⟩)

open OuterOddSubgroups.OverlapCentralizers

def permToEnd : Equiv.Perm (Fin 1600) →* Function.End (Fin 1600) where
  toFun p := p.toFun
  map_one' := rfl
  map_mul' _ _ := rfl

def pointGenerator (j : Fin 10) : Function.End (Fin 1600) := Packed.pointMap j

def normalMap (n : Fin 2048) : Function.End (Fin 1600) :=
  pointGenerator 2 ^ (n.val % 2) * pointGenerator 3 ^ (n.val / 2 % 2) *
  pointGenerator 4 ^ (n.val / 4 % 4) * pointGenerator 5 ^ (n.val / 16 % 2) *
  pointGenerator 6 ^ (n.val / 32 % 4) * pointGenerator 7 ^ (n.val / 128 % 2) *
  pointGenerator 8 ^ (n.val / 256 % 4) * pointGenerator 9 ^ (n.val / 1024 % 2)

theorem normalMap_eq (n : Fin 2048) : normalMap n = permToEnd (fastNormalForm n) := by
  simp only [fastNormalForm, map_mul, map_pow]
  rfl

public def evaluatedCoordinate (i : Fin 8192) (n : Fin 2048) : Fin 2048 :=
  let f := normalFormWord (normalMap (fastCandidatePair i).1)
    (normalMap (fastCandidatePair i).2) n
  decode (f 0) (f 930)

public theorem evaluatedCoordinate_eq (i : Fin 8192) (n : Fin 2048) :
    evaluatedCoordinate i n = coordinate (normalFormWord
      (fastNormalForm (fastCandidatePair i).1) (fastNormalForm (fastCandidatePair i).2) n) := by
  simp only [evaluatedCoordinate, normalMap_eq, ← map_normalFormWord]
  rfl

private def candidateIndex (a : Fin 128) (b : Fin 64) : Fin 8192 :=
  ⟨64 * a.val + b.val, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6400000 in
private theorem mask_rows (a : Fin 128) (b : Fin 64) :
    allowedIndex (candidateIndex a b) = true ∨
      label 0 (evaluatedCoordinate (candidateIndex a b) 37) ≠
        label 0 (evaluatedCoordinate (candidateIndex a b) 260) ∨
      label 1 (evaluatedCoordinate (candidateIndex a b) 4) ≠
        label 1 (evaluatedCoordinate (candidateIndex a b) 260) := by
  fin_cases a <;> revert b <;> apply Atlas1600OrderCertificate.allFin <;> decide +kernel

/-- On all candidate pairs, the two label equalities imply the published mask bit. -/
public theorem mask_check (i : Fin 8192)
    (h1 : label 0 (evaluatedCoordinate i 37) = label 0 (evaluatedCoordinate i 260))
    (h2 : label 1 (evaluatedCoordinate i 4) = label 1 (evaluatedCoordinate i 260)) :
    allowedIndex i = true := by
  let a : Fin 128 := ⟨i.val / 64, by omega⟩
  let b : Fin 64 := ⟨i.val % 64, by omega⟩
  have hi : candidateIndex a b = i := by
    apply Fin.ext
    dsimp [candidateIndex, a, b]
    omega
  have h := mask_rows a b
  rw [hi] at h
  rcases h with h | h | h
  · exact h
  · exact (h h1).elim
  · exact (h h2).elim

end Tits.SharpOuterBound.LocalImageBound.FusionElimination
