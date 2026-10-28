module

public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic.RankOne
public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic.Long
public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic.Short

/-!
# Solvable G₂ parabolic overgroups normalize their Sylow two-subgroup

Sylow conjugacy is performed inside the full parabolic containing the given
solvable subgroup. It transports its Sylow subgroup to the six positive root
groups while keeping the conjugated solvable subgroup in that same parabolic.
For fields of characteristic two and order greater than two, the two
standard-Sylow refinements put that conjugated subgroup in the Borel, which is
the normalizer of the positive-root Sylow subgroup. Transporting back proves
normalization of the original arbitrary ambient Sylow two-subgroup.

The rank-one matrix lemma is proved in `SolvableParabolic.RankOne`.
`SolvableParabolic.Short` applies it to the full short parabolic's plane action.
`SolvableParabolic.Long` uses the long-local quotient action and relative
normality to cover the full long parabolic. The theorem `normalizes` assembles
both refinements; it requires no additional geometric or Borel-containment premise.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), the characteristic-two paragraph for p = 3. This argument does
not invoke the p > 3 classification A.3.15.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace Atlas.G2.SolvableParabolic

private theorem sylow_conjugacy_in_overgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S T : Sylow p G) (P : Subgroup G)
    (hS : (S : Subgroup G) ≤ P) (hT : (T : Subgroup G) ≤ P) :
    ∃ g : P, (T : Subgroup G).map (MulAut.conj g.val).toMonoidHom = S := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P (T.subtype hT) (S.subtype hS)
  rw [Sylow.smul_subtype] at hg
  exact ⟨g, congrArg Sylow.toSubgroup (Sylow.subtype_injective hg)⟩

private theorem normalizes_of_standard_refinement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S T : Sylow p G) (P H : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hTH : (T : Subgroup G) ≤ H)
    (hH : Group.IsSolvable H) (hHP : H ≤ P)
    (hrefine : ∀ K : Subgroup G, (S : Subgroup G) ≤ K →
      Group.IsSolvable K → K ≤ P → K ≤ normalizer (S : Set G)) :
    H ≤ normalizer (T : Set G) := by
  obtain ⟨g,hg⟩ := sylow_conjugacy_in_overgroup S T P hSP (hTH.trans hHP)
  let e := MulAut.conj g.val
  let K := H.map e.toMonoidHom
  have hSK : (S : Subgroup G) ≤ K := by
    rw [← hg]
    exact map_mono hTH
  let _ : Group.IsSolvable H := hH
  have hK : Group.IsSolvable K := Group.isSolvable_of_surjective
    (f := (H.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
    (H.equivMapOfInjective e.toMonoidHom e.injective).surjective
  have hKP : K ≤ P := by
    rintro _ ⟨x,hx,rfl⟩
    exact P.mul_mem (P.mul_mem g.property (hHP hx)) (P.inv_mem g.property)
  have hn := hrefine K hSK hK hKP
  change K ≤ normalizer ((S : Subgroup G) : Set G) at hn
  rw [← hg, ← map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Conjugacy inside each full parabolic reduces the desired arbitrary-Sylow
normalization statement to the two standard positive-root Borel refinements. -/
theorem normalizes_of_standard_borel_refinements
    (hshort : ∀ K : Subgroup (Model F), unipotent ≤ K →
      Group.IsSolvable K → K ≤ parabolic₁ → K ≤ borel)
    (hlong : ∀ K : Subgroup (Model F), unipotent ≤ K →
      Group.IsSolvable K → K ≤ parabolic₂ → K ≤ borel)
    (T : Sylow 2 (Model F)) (H : Subgroup (Model F))
    (hTH : (T : Subgroup (Model F)) ≤ H) (hH : Group.IsSolvable H)
    (hP : H ≤ parabolic₁ ∨ H ≤ parabolic₂) : H ≤ normalizer (T : Set (Model F)) := by
  rcases hP with hP | hP
  · apply normalizes_of_standard_refinement sylow T parabolic₁ H
      (sylow_le_borel.trans borel_le_parabolic₁) hTH hH hP
    intro K hU hK hKP
    change K ≤ normalizer (unipotent (K := F) : Set (Model F))
    rw [SylowNormalizer.normalizer_unipotent]
    exact hshort K hU hK hKP
  · apply normalizes_of_standard_refinement sylow T parabolic₂ H
      (sylow_le_borel.trans borel_le_parabolic₂) hTH hH hP
    intro K hU hK hKP
    change K ≤ normalizer (unipotent (K := F) : Set (Model F))
    rw [SylowNormalizer.normalizer_unipotent]
    exact hlong K hU hK hKP

/-- Over a finite field of characteristic two and order greater than two, every
solvable subgroup containing an ambient Sylow two-subgroup and lying in either
full standard parabolic normalizes that Sylow subgroup. -/
theorem normalizes (hq : 2 < Nat.card F)
    (T : Sylow 2 (Model F)) (H : Subgroup (Model F))
    (hTH : (T : Subgroup (Model F)) ≤ H) (hH : Group.IsSolvable H)
    (hP : H ≤ parabolic₁ ∨ H ≤ parabolic₂) : H ≤ normalizer (T : Set (Model F)) :=
  normalizes_of_standard_borel_refinements
    (short_standard_le_borel hq) (long_standard_le_borel hq) T H hTH hH hP

end Atlas.G2.SolvableParabolic
