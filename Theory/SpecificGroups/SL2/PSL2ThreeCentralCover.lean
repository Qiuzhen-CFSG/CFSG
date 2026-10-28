module
public import Theory.SpecificGroups.SL2.BinaryTetrahedralCentralCover
public import Theory.GroupTheory.CentralCoverImage

/-!
# Nonsplit cyclic two-covers of PSL2 over a three-element field

A nonsplit central extension of PSL2(F), where F has three elements, by
an arbitrary nontrivial cyclic two-group contains a normal subgroup
isomorphic to SL2(F). This subgroup and the original kernel generate the
whole extension, and their intersection has order two.

Identify F with ZMod3 and transport the explicit binary tetrahedral matrix
model and its center quotient. The arbitrary central two-kernel embedding
theorem gives an actual binary tetrahedral subgroup, not a quotient of the
original extension. Its image is normal because it surjects modulo a
central kernel; the injective image preserves the two-element composite
kernel. The cyclicity and nontriviality assumptions are retained from the
source statement, although the stronger embedding argument needs neither.

This proves the exceptional q=3 Schur [26] step used in ABG II.3 Proposition
2, article p.22 (`refs/latex/alperin-brauer-gorenstein-pages/page-023.tex`).
In particular the cyclic kernel is not first reduced to order two, an
operation which could make a nonsplit extension split.
-/

namespace Matrix.ProjectiveSpecialLinearGroup

open GLS3.Chapter5.SchurPresentation

private noncomputable def slEquivOfCardThree {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3) : SL23 ≃* Matrix.SpecialLinearGroup (Fin 2) F := by
  let := Fintype.ofFinite F
  let e := ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  refine { Matrix.SpecialLinearGroup.map e.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
    left_inv := ?_
    right_inv := ?_ }
  · intro g
    ext i j
    exact e.symm_apply_apply (g i j)
  · intro g
    ext i j
    exact e.apply_symm_apply (g i j)

set_option linter.unusedVariables false in
public theorem exists_sl2_of_nonsplit_cyclic_two_cover_card_three
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3)
    {E : Type*} [Group E] [Finite E] (Z : Subgroup E) [Z.Normal]
    (hZnontrivial : Z ≠ ⊥) (hZcyclic : IsCyclic Z)
    (hZtwo : IsPGroup 2 Z) (hZcenter : Z ≤ Subgroup.center E)
    (e : E ⧸ Z ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hnosection : ¬ ∃ s : E ⧸ Z →* E,
      (QuotientGroup.mk' Z).comp s = MonoidHom.id _) :
    ∃ L : Subgroup E, L.Normal ∧
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
      Z ⊔ L = ⊤ ∧ Nat.card ↥(Z ⊓ L) = 2 := by
  let eSL := binaryTetrahedralEquivSL.trans (slEquivOfCardThree hF)
  have hecenter : (Subgroup.center BinaryTetrahedral).map eSL.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr eSL ⟨x, hx⟩).property
    · intro hy
      exact ⟨eSL.symm y, (Subgroup.centerCongr eSL.symm ⟨y, hy⟩).property,
        eSL.apply_symm_apply y⟩
  let eQ : BinaryTetrahedralCentralQuotient ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.congr _ _ eSL hecenter
  let c := e.trans eQ.symm
  let q := c.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hq : Function.Surjective q := c.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : q.ker = Z := by
    ext x
    change c ((QuotientGroup.mk' Z) x) = 1 ↔ x ∈ Z
    rw [c.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hqcenter : q.ker ≤ Subgroup.center E := hker ▸ hZcenter
  have hqtwo : IsPGroup 2 q.ker := hker ▸ hZtwo
  have hqnosection : ¬ ∃ s : BinaryTetrahedralCentralQuotient →* E,
      q.comp s = MonoidHom.id _ := by
    rintro ⟨s, hs⟩
    apply hnosection
    refine ⟨s.comp c.toMonoidHom, ?_⟩
    ext y
    apply c.injective
    exact DFunLike.congr_fun hs (c y)
  obtain ⟨f, hf, hfsurj, hfker⟩ :=
    exists_binaryTetrahedral_embedding_of_nonsplit q hq hqcenter hqtwo hqnosection
  obtain ⟨htop, hnormal, hcard⟩ := q.range_data_of_central_ker f hqcenter hfsurj hf
  refine ⟨f.range, hnormal, ⟨(MonoidHom.ofInjective hf).symm.trans eSL⟩, ?_, ?_⟩
  · simpa only [hker] using htop
  · simpa only [hker, hfker] using hcard

end Matrix.ProjectiveSpecialLinearGroup
