module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer.Coordinates
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OrdinaryComplement

/-!
# Pointwise fixers of Sylow two-subgroups of PSL₃ over even fields

Every automorphism fixing a Sylow two-subgroup pointwise is conjugation by
an element of that Sylow subgroup's center. Root orientation and coefficient
reconstruction supply coverage of all automorphisms, including fields of
orders two and four. The coordinate calculation then removes the field and
graph factors and identifies the remaining highest-root conjugation.

An actual isomorphism with the projective special linear group and Sylow
conjugacy transport both the automorphism and the relative center. No ambient
component hypotheses, assumed innerness, or assumed standard membership enter
the final result.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), the pointwise Sylow action used in
(!) and (*) and in the PSL₃ branch. This is the intrinsic fixer calculation,
not the remaining Borel action or the full E.6.8 assembly.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

/-- Every automorphism fixing the concrete upper unitriangular subgroup
pointwise is conjugation by an element of its highest-root subgroup. -/
theorem exists_projectiveCenter_of_fixes_unipotent {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (α : MulAut PSL(3,F))
    (hfix : ∀ u ∈ unipotent F, α u = u) :
    ∃ z ∈ projectiveCenter F, α = MulAut.conj z := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hn])
  let : CharP F 2 := ringChar.of_eq hc
  have hcover : standard F = ⊤ :=
    PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation F hn hF
      (PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F)
  exact PointwiseFixer.exists_projectiveCenter_of_mem_standard α
    (hcover.symm ▸ Subgroup.mem_top α) hfix

/-- Transport through an actual PSL₃ model and Sylow conjugacy identifies the
pointwise fixer of any specified Sylow two-subgroup, including q = 2 and q = 4. -/
theorem exists_sylow_center_conj_of_equiv {J : Type*} [Group J] [Finite J]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J) (α : MulAut J)
    (hfix : ∀ s ∈ S, α s = s) :
    ∃ z ∈ (center S).map (S : Subgroup J).subtype, α = MulAut.conj z := by
  let P := (unipotentSylow F hn hF).mapSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J P S
  let f : PSL(3,F) ≃* J := e.symm.trans (MulAut.conj g)
  have hS : (unipotent F).map f.toMonoidHom = (S : Subgroup J) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent F).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    change (unipotent F).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hh
  have hZ : (projectiveCenter F).map f.toMonoidHom =
      (center S).map (S : Subgroup J).subtype := by
    rw [projectiveCenter_eq_mapped_center, map_subgroup_center_eq _ f.injective, hS]
  let β : MulAut PSL(3,F) := (f.trans α).trans f.symm
  have hβfix : ∀ u ∈ unipotent F, β u = u := by
    intro u hu
    change f.symm (α (f u)) = u
    have hfu : f u ∈ (S : Subgroup J) := by
      rw [← hS]
      exact mem_map_of_mem f.toMonoidHom hu
    rw [hfix (f u) hfu]
    exact f.symm_apply_apply u
  obtain ⟨z,hz,hβ⟩ := exists_projectiveCenter_of_fixes_unipotent F hn hF β hβfix
  refine ⟨f z, hZ ▸ mem_map_of_mem f.toMonoidHom hz, ?_⟩
  ext x
  have hh := congrArg f (DFunLike.congr_fun hβ (f.symm x))
  change f (f.symm (α (f (f.symm x)))) = f (z * f.symm x * z⁻¹) at hh
  simpa only [f.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply] using hh

/-- The exact fixer description; the reverse implication is centrality inside
the specified Sylow subgroup, not centrality in the ambient group. -/
theorem fixes_sylow_iff_exists_center_conj_of_equiv {J : Type*} [Group J] [Finite J]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J) (α : MulAut J) :
    (∀ s ∈ S, α s = s) ↔
      ∃ z ∈ (center S).map (S : Subgroup J).subtype, α = MulAut.conj z := by
  constructor
  · exact exists_sylow_center_conj_of_equiv F hn hF e S α
  · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩ s hs
    have hc : s * (z : J) = (z : J) * s :=
      congrArg Subtype.val (mem_center_iff.mp hz ⟨s,hs⟩)
    change (z : J) * s * (z : J)⁻¹ = s
    rw [← hc, mul_inv_cancel_right]

end Matrix.PSL3.LinearThree
