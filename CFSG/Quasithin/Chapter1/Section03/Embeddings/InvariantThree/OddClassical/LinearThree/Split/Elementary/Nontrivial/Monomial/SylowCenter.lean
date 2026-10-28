module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.CubeLine
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.SylowCenter.Matrices
public import Theory.SpecificGroups.ProjectiveLinearInvolutions

/-!
# Position of the center of a monomial Sylow subgroup

The normal sign four-subgroup lies in the given ambient Sylow subgroup T.
Consequently every element of Z(T) has a diagonal lift. A transposition in
the coordinate image of T forces the two moved diagonal entries to agree.
The centralizer of the sign in the remaining coordinate therefore centralizes
all of Z(T), with both centralizers taken in the actual PSL₃ quotient.

This proves the coordinate-position premise used by the elementary monomial
intersection assembly. The geometry only needs odd field cardinality; the
prime and split congruence parameters are retained for that application.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial
open Matrix.SL3.SplitMonomial Matrix.PSL3.OuterSolvable.OddPrimeCoverage SylowCenter
variable {F : Type*} [Field F] [Finite F]

/-- A coordinate-sign centralizer centralizes the intrinsic center of the actual ambient Sylow. -/
theorem sylow_center_coordinate_position {p : ℕ} (hcard : Nat.card F = p)
    (_hp : p.Prime) (hodd : Odd p) (_hlarge : 3 < p) (_hmod : p % 3 = 1)
    (T : Sylow 2 PSL(3,F)) (hT : (T : Subgroup PSL(3,F)) ≤ projective F) :
    ∃ k : Fin 3, centralizer ({signElement (F := F) k} : Set PSL(3,F)) ≤
      centralizer ((center (T : Subgroup PSL(3,F))).map (T : Subgroup PSL(3,F)).subtype : Set PSL(3,F)) := by
  have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (hcard ▸ hodd)
  obtain ⟨t, k, ht, hk⟩ := sylow_has_transposition h2 T hT
  obtain ⟨g, hg, hgt⟩ := t.property
  change Matrix.PSL3.projection F g = t.val at hgt
  have hs := support_of_coordinateAction h2 (⟨g, hg⟩ : linear F) t hgt
  rw [hk] at hs
  refine ⟨k, ?_⟩
  intro x hx z hz
  obtain ⟨zT, hzT, rfl⟩ := hz
  obtain ⟨D, hDproj⟩ := Matrix.PSL3.projection_surjective F (zT : PSL(3,F))
  have hcomm (u : PSL(3,F)) (hu : u ∈ (T : Subgroup PSL(3,F))) :
      Commute (zT : PSL(3,F)) u := by
    exact (congrArg Subtype.val (mem_center_iff.mp hzT (⟨u, hu⟩ : T))).symm
  have hD : D.val = Matrix.diagonal (fun i => D i i) := by
    apply diagonal_of_commute_signs h2 D
    intro i
    rw [hDproj]
    exact hcomm _ (signs_le_sylow T hT i)
  have hd : ∀ i j, i ≠ k → j ≠ k → D i i = D j j := by
    apply repeated_diagonal_of_transposition D g k hD hs
    rw [hDproj, hgt]
    exact hcomm t.val ht
  obtain ⟨y, hy⟩ := Matrix.PSL3.projection_surjective F x
  have hycomm : Commute y (signSL k) := by
    apply commute_sign_of_projective y k
    rw [hy]
    exact mem_centralizer_singleton_iff.mp hx
  have he := congrArg (Matrix.PSL3.projection F) (commute_of_repeated_diagonal h2 D y k hD hd hycomm).eq
  change (zT : PSL(3,F)) * x = x * (zT : PSL(3,F))
  simpa only [map_mul, hDproj, hy] using he

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial
