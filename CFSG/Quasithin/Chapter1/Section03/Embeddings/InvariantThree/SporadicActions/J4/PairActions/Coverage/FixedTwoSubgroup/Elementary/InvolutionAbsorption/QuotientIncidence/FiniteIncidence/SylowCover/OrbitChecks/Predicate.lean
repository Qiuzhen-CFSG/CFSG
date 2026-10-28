module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.WordActions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.CoverData

/-!
# The pointwise orbit-certificate predicate

Each point check supplies sorted coordinates, a left-inverse lookup, and
an edge or a representative-root equality. Blocks prove this same predicate
on consecutive finite intervals; the interval helper loses no points.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover.OrbitChecks
open CoverData

def Valid (i : Fin 10395) : Prop :=
  (codes i).1.toNat ≤ (codes i).2.toNat ∧
  index (key (codes i)) = i ∧
  (if parent i < i then Step (codes (parent i)) (codes i) (sylowRows (letter i))
    else codes i = rootCodes (root i))

instance (i : Fin 10395) : Decidable (Valid i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem check_block {start len : ℕ}
    (h : ∀ k : Fin len, Valid (Fin.ofNat 10395 (start + k.val)))
    (i : Fin 10395) (hlo : start ≤ i.val) (hhi : i.val < start + len) : Valid i := by
  let k : Fin len := ⟨i.val - start, by omega⟩
  have hk : start + k.val = i.val := by dsimp [k]; omega
  have hp := h k
  rw [hk, Fin.ofNat_val_eq_self] at hp
  exact hp

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover.OrbitChecks
