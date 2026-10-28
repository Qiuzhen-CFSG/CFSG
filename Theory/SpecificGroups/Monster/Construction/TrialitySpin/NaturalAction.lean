module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinAction
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Natural

/-!
# The actual first natural representation of `N1`

The normal forms preserve the family of first-axis Golay coordinate
halfspaces, so the published signed halfspace construction gives an
unconditional 24-dimensional real representation of the concrete `N1`.
Fixing every signed halfspace is equivalent to fixing every point's Golay
projection. The structural axis theorem therefore identifies its kernel
with `Q1`. The action is monomial and preserves the normalized positive
form; `z1` is trivial and `ψ₂(sπ)` acts as minus identity.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.4 and Lemma 27.5(4),
printed pp. 146–147.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin.NaturalAction
open SignedModules.Natural

private theorem carries_mul {g h : Equiv.Perm Triple}
    (hg : Carries 0 0 g) (hh : Carries 0 0 h) : Carries 0 0 (g * h) := by
  intro l
  obtain ⟨m,hm⟩ := hh l
  obtain ⟨n,hn⟩ := hg m
  refine ⟨n,?_⟩
  change (g ∘ h) '' halfspace 0 l = _
  rw [Set.image_comp,hm,hn]

/-- Normalization is proved for the actual group, without a representation premise. -/
theorem preserves_halfspaces (g : N1) : Carries 0 0 (SpinAction.permutations g) := by
  obtain ⟨⟨d,e,α⟩,rfl⟩ := normalForm_bijective.surjective g
  exact carries_mul (carries_mul (standard_self_carries 0 α) (psi_carries 1 0 e))
    (psi_carries 0 0 d)

/-- The computed halfspace action of a collected triality word. -/
theorem normalForm_halfspace (d e : ParkerLoop) (α : ParkerStandardGroup)
    (x : Omega) (ε : ParkerBit) :
    SpinAction.permutations (normalForm d e α) '' halfspace 0 (x,ε) =
      halfspace 0 ((parkerStandardProjection α).val x, ε + e.1.val x) := by
  have h₁ : psi1 d '' halfspace 0 (x,ε) = halfspace 0 (x,ε) :=
    psi_self_halfspace 0 d (x,ε)
  have h₂ : psi2 e '' halfspace 0 (x,ε) = halfspace 0 (x,ε + e.1.val x) :=
    psi_other_halfspace 1 0 (by decide) e x ε
  have h₃ : psiAut1 α.val '' halfspace 0 (x,ε + e.1.val x) =
      halfspace 0 ((parkerStandardProjection α).val x,ε + e.1.val x) :=
    standard_self_halfspace 0 α x (ε + e.1.val x)
  change ((psiAut1 α.val ∘ psi2 e) ∘ psi1 d) '' halfspace 0 (x,ε) = _
  rw [Set.image_comp,h₁,Set.image_comp,h₂,h₃]

/-- The fixed natural module on the genuine first-axis coordinate halfspaces. -/
def representation : Representation ℝ N1 B1_24 :=
  SignedModules.Natural.representation SpinAction.permutations preserves_halfspaces

/-- The source signed-coordinate formula, now for the actual `N1` representation. -/
theorem representation_normalForm_L (d e : ParkerLoop) (α : ParkerStandardGroup)
    (x : Omega) (ε : ParkerBit) :
    representation (normalForm d e α) (L 0 ε x) =
      L 0 (ε + e.1.val x) ((parkerStandardProjection α).val x) := by
  change SignedModules.Natural.representation SpinAction.permutations preserves_halfspaces
    (normalForm d e α) (L 0 ε x) = _
  rw [SignedModules.Natural.representation_L,
    labelEquiv_of_image _ _ _ _ (normalForm_halfspace d e α x ε)]

private theorem fixes_halfspaces_of_mem_Q1 (g : N1) (hg : g.val ∈ Q1) :
    ∀ l, SpinAction.permutations g '' halfspace 0 l = halfspace 0 l := by
  intro l
  ext a
  constructor
  · rintro ⟨_,⟨d,hd,rfl⟩,rfl⟩
    obtain ⟨e,he,hcode⟩ := (Q1_axis1_characterization g.val g.prop).mp hg d
    change g.val.val (axis1 d) ∈ halfspace 0 l
    rw [he]
    apply (point_mem_halfspace 0 l e).mpr
    change d.1.val l.1 = l.2 at hd
    simpa only [hcode] using hd
  · rintro ⟨d,hd,rfl⟩
    change d.1.val l.1 = l.2 at hd
    obtain ⟨e,he,hcode⟩ := (Q1_axis1_characterization g.val⁻¹ (N1.inv_mem g.prop)).mp
      (Q1.inv_mem hg) d
    refine ⟨axis1 e, (point_mem_halfspace 0 l e).mpr ?_, ?_⟩
    · simpa only [hcode] using hd
    · change g.val.val (axis1 e) = axis1 d
      change g.val.val.symm (axis1 d) = axis1 e at he
      rw [← he,g.val.val.apply_symm_apply]

theorem representation_eq_one_iff (g : N1) : representation g = 1 ↔ g.val ∈ Q1 := by
  change SignedModules.Natural.representation SpinAction.permutations preserves_halfspaces g = 1 ↔ _
  rw [SignedModules.Natural.representation_kernel_iff]
  constructor
  · intro h
    apply (Q1_axis1_characterization g.val g.prop).mpr
    intro d
    have hi : SpinAction.permutations g (axis1 d) ∈ Set.range (point 0) := by
      rw [← image_axis (SpinAction.permutations g) (preserves_halfspaces g)]
      exact ⟨axis1 d,⟨d,rfl⟩,rfl⟩
    obtain ⟨e,he⟩ := hi
    refine ⟨e,he.symm,?_⟩
    apply Subtype.ext
    funext x
    have hm : SpinAction.permutations g (axis1 d) ∈ halfspace 0 (x,d.1.val x) := by
      rw [← h (x,d.1.val x)]
      exact ⟨axis1 d,(point_mem_halfspace 0 (x,d.1.val x) d).mpr rfl,rfl⟩
    rw [← he,point_mem_halfspace] at hm
    exact hm
  · exact fixes_halfspaces_of_mem_Q1 g

/-- Source 27.4(4), on the actual acting subgroup. -/
theorem representation_kernel : representation.ker = Q1.subgroupOf N1 := by
  ext g
  exact representation_eq_one_iff g

theorem representation_of_mem_Q1 (g : N1) (hg : g.val ∈ Q1) : representation g = 1 :=
  (representation_eq_one_iff g).mpr hg

theorem representation_z : representation SpinAction.z = 1 :=
  representation_of_z1 SpinAction.permutations preserves_halfspaces SpinAction.z rfl

theorem representation_c : representation SpinAction.c = -1 := by
  apply LinearMap.ext
  exact representation_of_psi2_signOmega SpinAction.permutations preserves_halfspaces
    SpinAction.c rfl

theorem representation_isometry (g : N1) (v w : B1_24) :
    form 0 (representation g v) (representation g w) = form 0 v w :=
  SignedModules.Natural.representation_isometry SpinAction.permutations preserves_halfspaces g v w

theorem representation_monomial (g : N1) (x : Omega) :
    ∃ y, representation g (basis 0 x) = basis 0 y ∨
      representation g (basis 0 x) = -basis 0 y :=
  SignedModules.Natural.representation_monomial SpinAction.permutations preserves_halfspaces g x

end Sporadic.Monster.Construction.TrialitySpin.NaturalAction
