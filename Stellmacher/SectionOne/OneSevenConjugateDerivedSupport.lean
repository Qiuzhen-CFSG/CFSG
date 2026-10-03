module
public import Stellmacher.SectionOne.OneSevenSupportTransitivity

/-!
# A selected support detected by its conjugate derived action

Let D be a one-seven factor and let both D and a subgroup R preserve M.
If the closure of the R-conjugates of D's derived subgroup acts nontrivially
on M, then the full four-element support of D lies in M.

A nonzero D-displacement of a member of M belongs to M and to D's support.
Transitivity on nonidentity support points then puts the whole support in M.
Otherwise D fixes M pointwise, and R-invariance makes every R-conjugate of
the derived subgroup fix M too, contrary to the given nontrivial action.

This is the implication V₁≤V_a at the start of the noncentral case of
Stellmacher (9.4), printed p.51/PDF p.41 of
`refs/files/stellmacher-n-group.pdf`. Its Section Nine consumer supplies
the literal quotient module, selected factor, and residual closure.
-/

namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_support_le_of_conjugate_derived_action
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D R : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (M : Subgroup V)
    (hDM : ∀ d ∈ D, ∀ v ∈ M, d • v ∈ M)
    (hRM : ∀ r ∈ R, ∀ v ∈ M, r • v ∈ M)
    (hactive : ¬ conjugateClosure ((commutator D).map D.subtype) R ≤
      fixingSubgroup G (M : Set V)) :
    commutatorAction D V ≤ M := by
  by_contra hnot
  have hfix : ∀ d ∈ D, ∀ v ∈ M, d • v = v := by
    intro d hd v hv
    by_contra hmove
    let delta := v⁻¹ * (d • v)
    have hdelta : delta ∈ M := M.mul_mem (M.inv_mem hv) (hDM d hd v hv)
    have hsupport : delta ∈ commutatorAction D V := by
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨d,hd⟩,v,rfl⟩
    have hne : delta ≠ 1 := fun heq => hmove (inv_mul_eq_one.mp heq).symm
    apply hnot
    intro w hw
    by_cases hw1 : w = 1
    · exact hw1 ▸ M.one_mem
    obtain ⟨a,ha,heq⟩ := oneSevenFactor_support_transitive D hD delta hsupport hne w hw hw1
    exact heq ▸ hDM a ha delta hdelta
  apply hactive
  apply (Subgroup.closure_le _).mpr
  rintro actor ⟨r,d,rfl⟩
  apply (mem_fixingSubgroup_iff G).mpr
  intro v hv
  have hrinv : (r:G)⁻¹ • v ∈ M := hRM (r:G)⁻¹ (R.inv_mem r.property) v hv
  have hdD : (d:G) ∈ D := (Subgroup.map_subtype_le _) d.property
  change ((r:G)*(d:G)*(r:G)⁻¹) • v = v
  rw [mul_smul,mul_smul,hfix (d:G) hdD _ hrinv,smul_inv_smul]

end Stellmacher.SectionOne
