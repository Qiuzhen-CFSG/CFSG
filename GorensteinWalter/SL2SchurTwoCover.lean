module

public import Theory.GroupTheory.Commutator.TwoCoverComparison
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Nonsplit cyclic two-covers of odd PSL2

For a finite field of odd order greater than three, a nonsplit central
extension of PSL2 by a nontrivial cyclic two-group has derived subgroup
isomorphic to SL2, meeting the given kernel in exactly two elements.
The original source hypotheses on the cyclic kernel are retained.

Nonsplitting and perfectness of the quotient force a nontrivial derived
kernel. Central Sylow transfer and the dihedral Sylow calculation bound
its order by two. The derived fiber product with the actual canonical
SL2 projective cover then identifies the two covers. This computes precisely
the needed two-primary part, uniformly including the field of order nine;
no full multiplier calculation or exceptional-field exclusion is assumed.

This is the Schur-cover step used in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 2 (article p.22). The general transfer,
dihedral, and fiber-product arguments live in Theory; this assembly uses
the existing Gorenstein--Walter intrinsic PSL2 Sylow models.
-/

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The derived subgroup of a nonsplit cyclic central two-cover of odd
PSL2(q), q > 3, is its canonical SL2 double cover, including q = 9. -/
public theorem commutator_equiv_specialLinearGroup_of_nonsplit_two_cover
    {E : Type*} [Group E] [Finite E]
    (F : Type*) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hcard : 3 < Nat.card F)
    (Z : Subgroup E) [Z.Normal]
    (_hZcyclic : IsCyclic Z) (_hZne : Z ≠ ⊥)
    (hZtwo : IsPGroup 2 Z) (hZcentral : Z ≤ Subgroup.center E)
    (e : E ⧸ Z ≃* ProjectiveSpecialLinearGroup (Fin 2) F)
    (hnonsplit : ¬ ∃ s : (E ⧸ Z) →* E,
      (QuotientGroup.mk' Z).comp s = MonoidHom.id (E ⧸ Z)) :
    Nonempty (_root_.commutator E ≃* SpecialLinearGroup (Fin 2) F) ∧
      Nat.card (Z ⊓ _root_.commutator E : Subgroup E) = 2 := by
  classical
  let g := GorensteinWalter.sl2ProjectiveProjection F
  obtain ⟨hg, hgcentral, hgcard, hg2, hperfect, hdihedral⟩ :=
    GorensteinWalter.sl2_projective_cover_model F hodd hcard
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) := hperfect
  let : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := g) hg
  let : Group.IsPerfect (E ⧸ Z) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let f : E →* ProjectiveSpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hfker : f.ker = Z := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hfcentral : f.ker ≤ Subgroup.center E := by simpa [hfker] using hZcentral
  have hf2 : IsPGroup 2 f.ker := by
    rw [hfker]
    exact hZtwo
  have hfn : f.ker ⊓ _root_.commutator E ≠ ⊥ := by
    rw [hfker]
    exact CentralExtension.quotientKernel_inf_commutator_ne_bot_of_no_section Z hnonsplit
  have hequiv : Nonempty (_root_.commutator E ≃* SpecialLinearGroup (Fin 2) F) :=
    CentralExtension.commutator_mulEquiv_of_central_two_covers
      f g hf hg hfcentral hgcentral hf2 hg2 hfn hgcard hdihedral
  let S : Sylow 2 E := Classical.choice Sylow.nonempty
  obtain ⟨n, hn, ⟨eS⟩⟩ := hdihedral (Sylow.mapSurjective hf S)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hbound := CentralExtension.card_ker_inf_commutator_le_two_of_dihedral_sylow
    f hf hfcentral hf2 S eS
  exact ⟨hequiv,
    CentralExtension.quotientKernel_inf_commutator_card_eq_two_of_no_section_of_card_le_two
      Z hnonsplit (by simpa [hfker] using hbound)⟩

end Matrix.ProjectiveSpecialLinearGroup
