module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives.Matrices

/-!
# Soundness of representative rank certificates

A witness records an intermediate matrix, row operations in both directions,
and a map from the intermediate matrix onto the rank-r diagonal matrix.
Four packed identities certify both rank inequalities. `matrix_contractionRows`
connects the input to the exact quartic, and `contractionRank_eq_rank` connects
matrix rank to the specified image dimension. Witness generation is untrusted;
only these identities are used.
-/

@[expose] public section
namespace BinaryQuarticMathieu.RankRecognition.Representatives

structure RankWitness where
  reduced : Rows
  forward : Rows
  backward : Rows
  right : Rows
  rank : Fin 11

/-- Forty ten-bit matrix rows followed by the candidate rank. The arithmetic
identities below validate the decoded fields; no property of the packing is
assumed. -/
def RankWitness.ofPacked (data : Nat) : RankWitness where
  reduced i := (data >>> (10 * i.val)) % 1024
  forward i := (data >>> (100 + 10 * i.val)) % 1024
  backward i := (data >>> (200 + 10 * i.val)) % 1024
  right i := (data >>> (300 + 10 * i.val)) % 1024
  rank := Fin.ofNat 11 (data >>> 400)

def ValidCertificate (c : Fin 3) (n : Word) (w : RankWitness) : Prop :=
  product w.forward (contractionRows c n) = w.reduced ∧
  product w.backward w.reduced = contractionRows c n ∧
  product (diagonalRows w.rank) w.reduced = w.reduced ∧
  product w.reduced w.right = diagonalRows w.rank

instance (c : Fin 3) (n : Word) (w : RankWitness) : Decidable (ValidCertificate c n w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem certificate_rank (c : Fin 3) (n : Word) (w : RankWitness)
    (h : ValidCertificate c n w) :
    contractionRank quartic (decode (representative c.succ)) (decode n) = w.rank.val := by
  rw [contractionRank_eq_rank, ← matrix_contractionRows]
  exact rank_eq_of_certificate _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

end BinaryQuarticMathieu.RankRecognition.Representatives
