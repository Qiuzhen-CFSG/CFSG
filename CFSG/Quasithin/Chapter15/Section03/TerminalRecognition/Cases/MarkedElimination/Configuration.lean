module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.LocalCores
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Source

/-!
# The marked exclusions on the existing source configuration

Use the genuine `SourceInput`, retaining both local groups, their actual
common Sylow subgroup, relative normality and residual identities. The
S₄ calculation applies to either labeling of two S₄ locals, as in
F.6.18(6) for L₃(2), A₆ and Â₆.

There is a separate obstruction useful for both A₇ labelings. The normal
closure V₀ strictly contains V: otherwise J(T_E) centralizes V₀ and hence
lies in Q₀. The identity X_E = [X_E,J(T_E)] would then put X_E in Q₀,
contrary to its cubic quotient. Since V is four-dimensional, V₀ has
dimension greater than four. Applying this to A₇ still requires extracting
its four-dimensional moved module from the full B.5.1 witness; we do not
assume that extraction is a consequence of an abstract group name.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66–68 and the final proof of 15.3.1, printed pp.1152–1155;
F.6.18, printed pp.309–310, and B.5.1, printed p.99.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination

open ExceptionalAction.ActionRecognition
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)
include d

/-- Apply the local contradiction without changing either source embedding. -/
theorem source_symmetricFour_excluded {K : Type*} [Group K]
    (e : coreQuotient H ≃* K)
    (localEquiv : (d.G1.map (e.toMonoidHom.comp coreProjection)) ≃*
      Equiv.Perm (Fin 4)) : False := by
  apply symmetricFour_local_excluded d.T d.YF V d.R d.F d.first_perfect
    (show (d.T : Subgroup H) ≤ normalizer (d.YF : Set H) from
      (d.first_local.symm ▸ le_sup_right).trans d.first_normalized)
    d.core_bound d.centralizer_eq.le
    (d.first_local ▸ d.local_commutator) d.singular_nontrivial e
  exact d.first_local ▸ localEquiv

/-- Both permitted generator labelings of the two S₄ locals are excluded.
The markings are equalities of images under the same quotient equivalence. -/
theorem source_symmetricFour_pair_excluded {K : Type*} [Group K]
    (e : coreQuotient H ≃* K) (P₁ P₂ : Subgroup K)
    (e₁ : P₁ ≃* Equiv.Perm (Fin 4)) (e₂ : P₂ ≃* Equiv.Perm (Fin 4))
    (marking :
      (d.G1.map (e.toMonoidHom.comp coreProjection) = P₁ ∧
        d.G2.map (e.toMonoidHom.comp coreProjection) = P₂) ∨
      (d.G1.map (e.toMonoidHom.comp coreProjection) = P₂ ∧
        d.G2.map (e.toMonoidHom.comp coreProjection) = P₁)) : False := by
  rcases marking with h | h
  · exact source_symmetricFour_excluded d e ((MulEquiv.subgroupCongr h.1).trans e₁)
  · exact source_symmetricFour_excluded d e ((MulEquiv.subgroupCongr h.1).trans e₂)

omit [Finite H] in
/-- The actual cubic quotient prevents the second factor from lying in Q₀. -/
theorem source_second_not_le_core : ¬ d.XE ≤ pCore 2 H := by
  intro h
  have hp : IsPGroup 2 d.XE := pCore_isPGroup.to_le h
  have hq := (hp.of_surjective (QuotientGroup.mk' (pCore 2 d.XE))
    (QuotientGroup.mk'_surjective _)).of_equiv d.second_odd_quotient.some
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have he : 3 = 2 ^ n := by simpa [Nat.card_eq_fintype_card] using hn
  have hn0 : n ≠ 0 := by intro h0; simp [h0] at he
  have hd : 2 ∣ 3 := he ▸ dvd_pow_self 2 hn0
  norm_num at hd

omit [Finite H] in
/-- The source vector group is properly contained in its normal closure. -/
theorem source_vector_lt_closure : V < moduleClosure V := by
  refine lt_of_le_of_ne le_normalClosure ?_
  intro he
  have hJR : Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H) ≤ d.R := by
    rw [d.sylow_thompson]
    exact sSup_le fun _ hA => hA.1
  have hJQ : Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H) ≤ pCore 2 H := by
    rw [← moduleClosure_centralizer V d.centralizer_isTwoGroup d.core_centralizes, ← he]
    exact hJR.trans d.centralizer_eq.le
  apply source_second_not_le_core d
  calc
    d.XE = ⁅d.XE, Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)⁆ :=
      d.second_commutator
    _ ≤ ⁅d.XE, pCore 2 H⁆ := commutator_mono le_rfl hJQ
    _ ≤ pCore 2 H := commutator_le_right _ _

variable [IsElementaryAbelian 2 (moduleClosure V)]

/-- The obstruction concerns the actual module V₀, in either local labeling. -/
theorem source_closure_finrank_gt_four :
    4 < Module.finrank (ZMod 2) (Additive (moduleClosure V)) := by
  have hne : planeSubspace V V ≠ ⊤ := by
    intro htop
    apply (source_vector_lt_closure d).ne
    apply le_antisymm le_normalClosure
    intro x hx
    have h : Additive.ofMul (⟨x, hx⟩ : moduleClosure V) ∈ planeSubspace V V := by
      rw [htop]
      trivial
    exact h
  have hdim := Submodule.finrank_lt hne
  rwa [d.vector_finrank] at hdim

/-- A four-dimensional classification of the whole moved source module is
incompatible with the source configuration. Its construction remains separate. -/
theorem source_fourDimensional_excluded
    (dimension : Module.finrank (ZMod 2) (Additive (moduleClosure V)) = 4) : False := by
  have h := source_closure_finrank_gt_four d
  omega

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination
