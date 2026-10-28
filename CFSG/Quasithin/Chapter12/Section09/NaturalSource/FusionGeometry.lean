module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Stages

/-!
# The opening fixed-point argument of 12.9.9

Apply the proved intersection theorem 12.9.8 to A = Vᵍ ∩ N_G(L) ≤ T.
When [A,V] is nontrivial, A ∩ V is trivial, so N_V(A) = C_V(A).
Transporting the noncyclic-subspace normalizer bound to Vᵍ then shows
C_V(B) = C_V(A) for every B ≤ A of order greater than two. Consequently
C_A(W) has order at most two whenever W ≤ V is not centralized by A.

These deductions use the actual local normalizer bounds from 12.9.7.
They do not assert the later weak-closure or hyperplane conclusions.
Source: Aschbacher--Smith, printed pp.862--863 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Transport normalizer control using the source's right-conjugation convention. -/
theorem normalizer_control_conjugate {V : Subgroup G}
    (control : ∀ B : Subgroup G, B ≤ V → 2 < Nat.card B →
      normalizer (B : Set G) ≤ normalizer (V : Set G))
    (g : G) (B : Subgroup G) (hB : B ≤ conjugate V g) (hc : 2 < Nat.card B) :
    normalizer (B : Set G) ≤ normalizer (conjugate V g : Set G) := by
  have hbV : conjugate B g⁻¹ ≤ V := by
    have hm : conjugate B g⁻¹ ≤ conjugate (conjugate V g) g⁻¹ := map_mono hB
    have he := conjugate_conjugate_inv V g⁻¹
    simp only [inv_inv] at he
    exact hm.trans he.le
  have hcb : 2 < Nat.card (conjugate B g⁻¹) := by
    change 2 < Nat.card (B.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom)
    rwa [card_map_of_injective (MulAut.conj _).injective]
  have hmap := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (control _ hbV hcb)
  simp only [map_equiv_normalizer_eq] at hmap
  change normalizer (conjugate (conjugate B g⁻¹) g : Set G) ≤
    normalizer (conjugate V g : Set G) at hmap
  simpa only [conjugate_conjugate_inv] using hmap

variable {X : Type u} [Group X] [Finite X]
variable {K : GroupClass.{u}} {T : Sylow 2 X} {L V : Subgroup X} {n : ℕ}

/-- The common fixed subgroup in the first paragraph of the proof of 12.9.9. -/
theorem common_fixed_subgroups (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set X)) V)
    (g : X) (hAT : conjugate V g ⊓ normalizer (L : Set X) ≤ (T : Subgroup X))
    (hnoncomm : ⁅conjugate V g ⊓ normalizer (L : Set X), V⁆ ≠ ⊥) :
    let A := conjugate V g ⊓ normalizer (L : Set X)
    A ⊓ V = ⊥ ∧ V ⊓ normalizer (A : Set X) = V ⊓ centralizer (A : Set X) ∧
      ∀ B : Subgroup X, B ≤ A → 2 < Nat.card B →
        V ⊓ centralizer (B : Set X) = V ⊓ centralizer (A : Set X) := by
  dsimp only
  let A := conjugate V g ⊓ normalizer (L : Set X)
  obtain ⟨_, intersections, normalizers⟩ :=
    source_intersections_of_local_geometry h earlier F hab control
  have hAN : A ≤ normalizer (V : Set X) := hAT.trans (h.sylow_normalizes_seed earlier.structural)
  have hVM : V ≤ normalizer (L : Set X) :=
    h.chosen.le_sylow.trans (h.sylow_normalizes earlier.structural)
  have hdis : A ⊓ V = ⊥ := by
    by_contra hne
    have hinter : V ⊓ conjugate V g ≠ ⊥ := by
      intro he
      apply hne
      apply le_bot_iff.mp
      rw [← he]
      exact le_inf inf_le_right (inf_le_left.trans inf_le_left)
    apply hnoncomm
    apply le_bot_iff.mp
    rw [← intersections g hinter, commutator_comm V]
    exact commutator_mono inf_le_left le_rfl
  have hfix : V ⊓ normalizer (A : Set X) = V ⊓ centralizer (A : Set X) := by
    apply le_antisymm ?_ (inf_le_inf_left V (Subgroup.centralizer_le_normalizer _))
    apply le_inf inf_le_left
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hdis]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp inf_le_right)
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hAN))
  refine ⟨hdis, hfix, ?_⟩
  intro B hBA hc
  apply le_antisymm ?_ (inf_le_inf_left V (centralizer_le hBA))
  rw [← hfix]
  apply le_inf inf_le_left
  have hBN : normalizer (B : Set X) ≤ normalizer (conjugate V g : Set X) :=
    normalizer_control_conjugate normalizers g B (hBA.trans inf_le_left) hc
  exact (le_inf (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hBN))
    ((inf_le_left.trans hVM).trans (normalizer (L : Set X)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

omit [Finite X] in
/-- The remaining assertion of that paragraph, in group-order form. -/
theorem centralizer_card_le_two_of_common_fixed {A W : Subgroup X} (hWV : W ≤ V) (hmoves : ¬ W ≤ centralizer (A : Set X))
    (hfixed : ∀ B : Subgroup X, B ≤ A → 2 < Nat.card B →
      V ⊓ centralizer (B : Set X) = V ⊓ centralizer (A : Set X)) :
    Nat.card (A ⊓ centralizer (W : Set X) : Subgroup X) ≤ 2 := by
  by_contra! hbig
  apply hmoves
  have he := hfixed (A ⊓ centralizer (W : Set X)) inf_le_left hbig
  have hW : W ≤ V ⊓ centralizer (A ⊓ centralizer (W : Set X) : Set X) :=
    le_inf hWV (le_centralizer_iff.mp inf_le_right)
  exact (hW.trans he.le).trans inf_le_right

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
