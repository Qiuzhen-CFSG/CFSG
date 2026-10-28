module

public import Theory.SpecificGroups.HaradaNorton.Simplicity.WordCertificates.PackedRows

/-!
# Checking commutation with packed rows

Equality of the two packed row products implies commutation of the decoded
matrices. This avoids storing redundant product witnesses for the distant
Suzuki generators. Soundness follows from `entry_rowProduct`.
-/

public section
namespace HaradaNorton.OrderCertificate.LocalRelationChecks

open HaradaNorton.WordCertificates

/-- A rowwise packed commutation check proves ordinary matrix commutation. -/
theorem decode_commute (a b : Nat → Row)
    (h : ∀ i : Fin 133, rowProduct (a i.val) b 133 = rowProduct (b i.val) a 133) :
    Commute (decode a) (decode b) := by
  change decode a * decode b = decode b * decode a
  apply Matrix.ext
  intro i j
  change (∑ k : Fin 133, entry (a i.val) k.val * entry (b k.val) j.val) =
    ∑ k : Fin 133, entry (b i.val) k.val * entry (a k.val) j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => entry (a i.val) k * entry (b k) j.val),
    Fin.sum_univ_eq_sum_range (fun k => entry (b i.val) k * entry (a k) j.val),
    ← entry_rowProduct, ← entry_rowProduct, h i]

end HaradaNorton.OrderCertificate.LocalRelationChecks
