module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.DoubleCosetCover.Soundness

/-!
# Soundness of packed core-transition checks

The checker evaluates core words using arbitrary point maps. Once those maps
are proved equal to the six signed core generators, agreement at the certified
base 0, 1, 2 proves the transition equations in the actual Atlas group.
Tables are divided into 50 blocks of 64 entries to bound kernel computation.

Source: the primary ATLAS max1 and max2 words in `MinimumIndex/source/`.
-/

namespace Tits.MinimumIndexThirteen.CandidateRigidity.CoreCover
open Theory.GroupTheory Atlas1600OrderCertificate

/-- Evaluate a word of point maps, in the same left-action convention as evalWord. -/
@[expose] public def applyWord (f : Fin 6 → Fin 1600 → Fin 1600) :
    List (Fin 6) → Fin 1600 → Fin 1600
  | [], p => p
  | k :: w, p => f k (applyWord f w p)

public theorem applyWord_eq (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (hf : ∀ k p, f k p = (signedCore i k).val p) (w : List (Fin 6)) (p : Fin 1600) :
    applyWord f w p = (evalWord (signedCore i) w).val p := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change f k (applyWord f w p) = (signedCore i k).val ((evalWord (signedCore i) w).val p)
    rw [hf, ih]

@[expose] public def applyNode (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (c : Nat) (p : Fin 1600) : Fin 1600 :=
  packedRepresentative i (repIndex c) (applyWord f (word (c / 8)) p)

public theorem applyNode_eq (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (hf : ∀ k p, f k p = (signedCore i k).val p) (c : Nat) (p : Fin 1600) :
    applyNode i f c p = (node i c).val p := by
  rw [applyNode, packed_representative, applyWord_eq i f hf]
  rfl

/-- One transition is checked at the faithful three-point base. -/
@[expose] public def test (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (t : Table) (k : Fin 2) (r : Fin 3200) : Bool :=
  checkFin fun p : Fin 3 =>
    decide (applyNode i f (t.nodes r) (L0Gen (k.castLE (by decide)) (p.castLE (by decide))) =
      applyWord f (word (t.transitions k r / 4096))
        (applyNode i f (t.nodes (destination (t.transitions k r))) (p.castLE (by decide))))

public theorem steps_of_test (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (hf : ∀ k p, f k p = (signedCore i k).val p) (t : Table)
    (ht : ∀ k r, test i f t k r = true) : Steps i t := by
  intro k r
  have hp (p : Fin 3) := of_decide_eq_true ((checkFin_spec _).mp (ht k r) p)
  simp only [applyNode_eq i f hf, applyWord_eq i f hf, packed_standard] at hp
  exact ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext (hp 0) (hp 1) (hp 2)

/-- Each block has 64 nodes; the packed widths accommodate the discovered words. -/
@[expose] public def packedTable (ns ts : Nat → Nat) : Table where
  nodes r := (ns (r.val / 64) >>> (40 * (r.val % 64))) % 2^40
  transitions k r :=
    (ts (r.val / 64) >>> (112 * (r.val % 64) + 56 * k.val)) % 2^56

@[expose] public def blockIndex (b : Fin 50) (r : Fin 64) : Fin 3200 :=
  ⟨64 * b.val + r.val, by omega⟩

/-- A bounded check is the computational unit, separate from its data module. -/
@[expose] public def testBlock (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (t : Table) (b : Fin 50) : Bool :=
  checkFin fun k : Fin 2 => checkFin fun r : Fin 64 => test i f t k (blockIndex b r)

public theorem test_of_blocks (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (t : Table) (hb : ∀ b, testBlock i f t b = true) (k : Fin 2) (r : Fin 3200) :
    test i f t k r = true := by
  let b : Fin 50 := ⟨r.val / 64, by omega⟩
  let s : Fin 64 := ⟨r.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : blockIndex b s = r := by apply Fin.ext; dsimp [blockIndex, b, s]; omega
  rw [← he]
  exact (checkFin_spec _).mp ((checkFin_spec _).mp (hb b) k) s

/-- Apply a complete packed certificate to the exact cover required by rigidity. -/
public theorem cover_of_blocks (i : Fin 2) (f : Fin 6 → Fin 1600 → Fin 1600)
    (hf : ∀ k p, f k p = (signedCore i k).val p) (t : Table)
    (hzero : t.nodes 0 = 0) (hb : ∀ b, testBlock i f t b = true)
    (x : Atlas1600Group) :
    ∃ (a b : core (i.castLE (by decide))) (j : Fin 6),
      x = a.val * representative i j * b.val :=
  cover_of_steps i t hzero (steps_of_test i f hf t (test_of_blocks i f t hb)) x

end Tits.MinimumIndexThirteen.CandidateRigidity.CoreCover
