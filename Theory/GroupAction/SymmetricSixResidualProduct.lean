module
public import Theory.GroupTheory.Commutator.NormalizedJoinCard
public import Theory.GroupAction.SymmetricSixSmallSection

/-!
# A product bound for residual commutators above S₆

Let M have a symmetric-six quotient with two-group kernel Q, and let
M = O²(M) R with Q contained in R. If D is an R-invariant subgroup of Q,
then adjoining C = [Q,O²(M)] makes D C normal in M. The derived order of
this join is at most |D′| |C′| |[D,C]|. When this product is at most eight,
the small normal-section theorem makes O²(M) centralize D′.

The estimate keeps the full residual core C. It needs no identification of
[C,D] with C′ and no separate bounds on the three factors.
Source application: MS93 (3.10) and the terminal argument of (5.12),
printed pp.879--881 and 927.
-/

public section
open scoped commutatorElement
namespace Subgroup

/-- Adjoining the full residual core to an edge-normalized kernel makes
a normal subgroup. A product-order bound forces its derived subgroup to
be fixed by the two-residual of the symmetric-six extension. -/
theorem derived_centralizes_residual_of_symmetricSix_product
    {M : Type*} [Group M] [Finite M]
    (q : M →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (R D : Subgroup M)
    (hKR : q.ker ≤ R) (hgen : pResidual 2 M ⊔ R = ⊤)
    (hDK : D ≤ q.ker) (hDN : R ≤ normalizer (D : Set M))
    (hproduct :
      Nat.card (⁅D,D⁆ : Subgroup M) *
        Nat.card (⁅⁅q.ker,pResidual 2 M⁆,⁅q.ker,pResidual 2 M⁆⁆ : Subgroup M) *
        Nat.card (⁅D,⁅q.ker,pResidual 2 M⁆⁆ : Subgroup M) ≤ 8) :
    ⁅D,D⁆ ≤ centralizer (pResidual 2 M : Set M) := by
  let C := ⁅q.ker,pResidual 2 M⁆
  let N := D ⊔ C
  have hCK : C ≤ q.ker := commutator_le_left _ _
  have hCN : C ≤ normalizer (D : Set M) := (hCK.trans hKR).trans hDN
  have hnormal : (⊤ : Subgroup M) ≤ normalizer (N : Set M) := by
    rw [←hgen]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      exact (commutator_mono (sup_le hDK hCK) le_rfl).trans le_sup_right
    · exact (le_inf hDN (le_normalizer_of_normal (H := C))).trans
        (normalizer_inf_normalizer_le_normalizer_sup D C)
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique hnormal)
  have hcard : Nat.card (⁅N,N⁆ : Subgroup M) ≤ 8 :=
    (commutator_sup_card_le_of_mutual_normalization D C
      le_normalizer_of_normal hCN).trans hproduct
  have hNK : ⁅N,N⁆ ≤ q.ker :=
    (show ⁅N,N⁆ ≤ N from commutator_le_left _ _).trans (sup_le hDK hCK)
  have hh := commutator_pResidual_le_of_symmetricSix_small_section
    q hq hker ⁅N,N⁆ ⊥ hNK (by simpa only [relIndex_bot_left] using hcard)
  exact commutator_eq_bot_iff_le_centralizer.mp
    (le_bot_iff.mp ((commutator_mono (commutator_mono le_sup_left le_sup_left)
      le_rfl).trans hh))

end Subgroup
