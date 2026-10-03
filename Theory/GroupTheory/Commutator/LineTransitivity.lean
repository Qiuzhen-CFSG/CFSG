module
public import Theory.GroupTheory.Commutator.LinePermutation
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Transitivity of commutator lines from one spanning module

Suppose S normalizes B, T lies in B, and V is the join of the S-conjugates
of M. If both [M,B] and [V,T] have order two, then [V,T] is an S-conjugate
of [M,B]. No factor permutation hypothesis is required.

Nontriviality of [V,T] forces some [M^s,T] to be nontrivial. This subgroup
lies both in [V,T] and in [M,B]^s. Their order-two cardinalities force
equality. This is the line-orbit step after selected-module spanning in
Stellmacher (4.6), journal p26; refs/latex/stellmacher-n-group.tex.
-/

namespace Subgroup

public theorem exists_conjugate_commutator_line_of_spanning
    {G : Type*} [Group G] [Finite G]
    (B V M T S : Subgroup G)
    (hSB : S ≤ normalizer (B : Set G)) (hTB : T ≤ B)
    (hline : Nat.card (⁅M, B⁆ : Subgroup G) = 2)
    (hcoord : Nat.card (⁅V, T⁆ : Subgroup G) = 2)
    (hspan : V = ⨆ s : S, M.map (MulAut.conj (s : G)).toMonoidHom) :
    ∃ s : S, (⁅M, B⁆).map (MulAut.conj (s : G)).toMonoidHom = ⁅V, T⁆ := by
  classical
  have hne : ⁅V, T⁆ ≠ ⊥ := by
    intro h
    have hone := card_eq_one.mpr h
    omega
  have hex : ∃ s : S, ⁅M.map (MulAut.conj (s : G)).toMonoidHom, T⁆ ≠ ⊥ := by
    by_contra hn
    have hcent : V ≤ centralizer (T : Set G) := by
      rw [hspan]
      apply iSup_le
      intro s
      apply commutator_eq_bot_iff_le_centralizer.mp
      by_contra hbad
      exact hn ⟨s, hbad⟩
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr hcent)
  obtain ⟨s, hs⟩ := hex
  let α := MulAut.conj (s : G)
  let C := ⁅M.map α.toMonoidHom, T⁆
  let R := (⁅M, B⁆).map α.toMonoidHom
  have hB : B.map α.toMonoidHom = B := by
    apply le_antisymm
    · rintro x ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp (hSB s.property) b).mp hb
    · intro b hb
      have hc : (s : G)⁻¹ * b * s ∈ B :=
        by simpa only [inv_inv] using
          (mem_normalizer_iff.mp (hSB (S.inv_mem s.property)) b).mp hb
      refine ⟨(s : G)⁻¹ * b * s, hc, ?_⟩
      simp [α, MulAut.conj_apply, mul_assoc]
  have hCR : C ≤ R := by
    dsimp [C, R]
    rw [map_commutator]
    change ⁅M.map α.toMonoidHom, T⁆ ≤ ⁅M.map α.toMonoidHom, B.map α.toMonoidHom⁆
    rw [hB]
    exact commutator_mono le_rfl hTB
  have hCV : C ≤ ⁅V,T⁆ := commutator_mono
    (hspan ▸ (le_iSup (fun s : S => M.map (MulAut.conj (s : G)).toMonoidHom) s)) le_rfl
  have hRc : Nat.card R = 2 := by
    rw [show R = (⁅M,B⁆).map α.toMonoidHom from rfl, card_map_of_injective α.injective]
    exact hline
  have hCtwo : 2 ≤ Nat.card C := by
    by_contra hn
    exact hs (eq_bot_of_card_le C (by omega))
  have hCR_eq : C = R := eq_of_le_of_card_ge hCR (by rw [hRc]; exact hCtwo)
  have hCV_eq : C = ⁅V,T⁆ := eq_of_le_of_card_ge hCV (by rw [hcoord]; exact hCtwo)
  exact ⟨s, hCR_eq.symm.trans hCV_eq⟩

end Subgroup
