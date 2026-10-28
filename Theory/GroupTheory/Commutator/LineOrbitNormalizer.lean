module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Data.Finite.Defs

/-!
# A support sum normalized by a stabilizer supplement

Let pairwise disjoint subgroups Mi inside B generate V, with the
centralizer of V in B contained in V and each [Mi,B] contained in Mi.
Let S normalize V, and suppose S-conjugates of a selected support
generate V. If U normalizes B and the selected commutator line, and the
selected support commutes with its U-conjugates, a literal factorization
C = U S implies that C normalizes V.

For u in U, the commutator of Mi0^u with any other support lies in both
corresponding disjoint supports, so is trivial. The supplied self-coordinate
commutativity then makes Mi0^u centralize V; self-centralization inside B
puts Mi0^u in V. Inverting C = U S gives C = S U, hence every C-conjugate
of Mi0 lies in V. Finally the S-spanning hypothesis implies C normalizes V.

This isolates the last orbit argument in Stellmacher (4.6), Journal of
Algebra 190 (1997), p26, refs/latex/stellmacher-n-group.tex. Oddness of U
is used by the caller's coprime-action result to supply commutativity;
the orbit argument itself needs only the displayed group hypotheses.
-/

open scoped Pointwise
namespace Subgroup

/-- A commuting selected-support orbit and a stabilizer supplement normalize the full support sum. -/
public theorem line_family_odd_orbit_normalizes
    {G I : Type*} [Group G] [Finite G]
    (B V S C U : Subgroup G) (M : I → Subgroup G) (i0 : I)
    (hMB : ∀ i, M i ≤ B) (hV : V = ⨆ i, M i)
    (hdisj : Pairwise fun i j => Disjoint (M i) (M j))
    (hline : ∀ i, ⁅M i, B⁆ ≤ M i)
    (hcentral : B ⊓ centralizer (V : Set G) ≤ V)
    (hSV : S ≤ normalizer (V : Set G))
    (hspan : V = ⨆ s : S, (M i0).map (MulAut.conj (s : G)).toMonoidHom)
    (hU : U ≤ normalizer (B : Set G) ⊓ normalizer ((⁅M i0, B⁆ : Subgroup G) : Set G))
    (hself : ∀ u ∈ U, ⁅M i0, (M i0).map (MulAut.conj u).toMonoidHom⁆ = ⊥)
    (hprod : (C : Set G) = (U : Set G) * (S : Set G)) :
    C ≤ normalizer (V : Set G) := by
  have hUm (u : G) (hu : u ∈ U) : (M i0).map (MulAut.conj u).toMonoidHom ≤ V := by
    let A := (M i0).map (MulAut.conj u).toMonoidHom
    have hBm : B.map (MulAut.conj u).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp (hU hu).1
    have hRm : (⁅M i0, B⁆).map (MulAut.conj u).toMonoidHom = ⁅M i0, B⁆ :=
      mem_normalizer_iff_map_conj_eq.mp (hU hu).2
    have hAB : A ≤ B := by
      rw [← hBm]
      exact map_mono (hMB i0)
    have hAR : ⁅A, B⁆ = ⁅M i0, B⁆ := by
      rw [map_commutator, hBm] at hRm
      exact hRm
    have hcross (j : I) : ⁅M j, A⁆ = ⊥ := by
      by_cases hj : j = i0
      · subst j
        exact hself u hu
      · apply le_bot_iff.mp
        apply (le_inf ?_ ?_).trans (hdisj hj).le_bot
        · exact (commutator_mono le_rfl hAB).trans (hline j)
        · rw [commutator_comm]
          exact (commutator_mono le_rfl (hMB j)).trans (hAR.le.trans (hline i0))
    have hVA : V ≤ centralizer (A : Set G) := by
      rw [hV]
      exact iSup_le fun j => commutator_eq_bot_iff_le_centralizer.mp (hcross j)
    exact (le_inf hAB (le_centralizer_iff.mp hVA)).trans hcentral
  have hSC : S ≤ C := by
    intro s hs
    change s ∈ (C : Set G)
    rw [hprod]
    exact Set.mem_mul.mpr ⟨1, U.one_mem, s, hs, one_mul s⟩
  have hCm (c : G) (hc : c ∈ C) (m : G) (hm : m ∈ M i0) : c * m * c⁻¹ ∈ V := by
    have hci : c⁻¹ ∈ (U : Set G) * (S : Set G) := hprod ▸ C.inv_mem hc
    obtain ⟨u, hu, s, hs, hus⟩ := Set.mem_mul.mp hci
    have hmu : u⁻¹ * m * u ∈ V := by
      have hh := hUm u⁻¹ (U.inv_mem hu) (mem_map_of_mem (MulAut.conj u⁻¹).toMonoidHom hm)
      change u⁻¹ * m * (u⁻¹)⁻¹ ∈ V at hh
      simpa only [inv_inv] using hh
    have hsv := (mem_normalizer_iff.mp (hSV (S.inv_mem hs)) (u⁻¹ * m * u)).mp hmu
    have heq : c = s⁻¹ * u⁻¹ := by
      have he := congrArg Inv.inv hus
      simpa only [mul_inv_rev, inv_inv] using he.symm
    simpa only [heq, mul_inv_rev, inv_inv, mul_assoc] using hsv
  apply le_normalizer_iff.mpr
  intro c hc v hv
  have hmap : V.map (MulAut.conj c).toMonoidHom ≤ V := by
    nth_rw 1 [hspan]
    rw [map_iSup]
    apply iSup_le
    intro s
    rintro x ⟨a, ha, rfl⟩
    obtain ⟨m, hm, rfl⟩ := ha
    have hh := hCm (c * (s : G)) (C.mul_mem hc (hSC s.property)) m hm
    change c * ((s : G) * m * (s : G)⁻¹) * c⁻¹ ∈ V
    simpa only [mul_inv_rev, mul_assoc] using hh
  exact hmap (mem_map_of_mem (MulAut.conj c).toMonoidHom hv)

end Subgroup

