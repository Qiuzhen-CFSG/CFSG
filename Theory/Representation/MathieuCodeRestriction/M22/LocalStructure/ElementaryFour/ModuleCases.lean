module

public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.GeneratedSubgroupInvariants

/-!
# Fixed-space deductions for the elementary-four cases

Conjugation transports the actual sum of element fixed spaces. A normalizing
subgroup therefore preserves this sum. An irreducible quotient makes the sum
all of the module once a second element has fixed vectors outside the first
fixed space. In the rank-three intersection case, the two relevant spaces
have dimensions five and seven and meet in dimension three, so their sum has
codimension one in the ten-dimensional module.

These are the linear-algebra deductions in Aschbacher--Smith H.15.5,
combined manuscript (1 March 2004), printed p.401. The local group identities
and the earlier module dimensions remain explicit inputs.
-/

@[expose] public section

open Representation.BinaryOffender
namespace MathieuCode.M22ElementaryFour
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem fixedSpaceSpan_map_conj (A : Subgroup G) (g : G) :
    (fixedSpaceSpan ρ A).map (ρ g) =
      fixedSpaceSpan ρ (A.map (MulAut.conj g).toMonoidHom) := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  apply fixedSpaceSpan_map_equivariant ρ ρ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective e
  intro a v
  change ρ g (ρ a v) = ρ (g * a * g⁻¹) (ρ g v)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem fixedSpaceSpan_invariant (A X : Subgroup G)
    (hXA : X ≤ Subgroup.normalizer A) :
    X ≤ subspaceStabilizer ρ (fixedSpaceSpan ρ A) := by
  apply le_subspaceStabilizer
  intro g hg v hv
  have he := fixedSpaceSpan_map_conj ρ A g
  have hgA : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXA hg)
  rw [hgA] at he
  exact he ▸ Submodule.mem_map_of_mem hv

theorem fixedSpaceSpan_eq_top_of_irreducible_interval
    (A X : Subgroup G) (i z : G) (hi : i ∈ A) (hi1 : i ≠ 1)
    (hz : z ∈ A) (hz1 : z ≠ 1)
    (hXA : X ≤ Subgroup.normalizer A)
    (hnot : ¬ fixedSpace ρ (Subgroup.zpowers z) ≤ fixedSpace ρ (Subgroup.zpowers i))
    (hirr : ∀ U : Submodule (ZMod 2) V,
      X ≤ subspaceStabilizer ρ U → fixedSpace ρ (Subgroup.zpowers i) ≤ U →
      U = fixedSpace ρ (Subgroup.zpowers i) ∨ U = ⊤) :
    fixedSpaceSpan ρ A = ⊤ := by
  have hU := fixedSpace_le_fixedSpaceSpan ρ hi hi1
  have hZ := fixedSpace_le_fixedSpaceSpan ρ hz hz1
  rcases hirr _ (fixedSpaceSpan_invariant ρ A X hXA) hU with he | he
  · exact (hnot (he ▸ hZ)).elim
  · exact he

theorem fixedSpace_le_span_of_nontrivial (A : Subgroup G) (hA : A ≠ ⊥) :
    fixedSpace ρ A ≤ fixedSpaceSpan ρ A := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hle : Subgroup.zpowers (a : G) ≤ A := Subgroup.zpowers_le.mpr a.property
  exact (ρ.invariants_comp_subtype_antitone hle).trans
    (fixedSpace_le_fixedSpaceSpan ρ a.property ha1)

theorem rank_three_module_case [FiniteDimensional (ZMod 2) V]
    (A B : Subgroup G) (i : G) (hA : A = B ⊔ Subgroup.zpowers i)
    (hB : B ≠ ⊥) (hi1 : i ≠ 1)
    (U : Submodule (ZMod 2) V) (hBU : fixedSpace ρ B = U)
    (hdV : Module.finrank (ZMod 2) V = 10)
    (hdU : Module.finrank (ZMod 2) U = 5)
    (hdi : Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers i)) = 7)
    (hdint : Module.finrank (ZMod 2)
      ↥(U ⊓ fixedSpace ρ (Subgroup.zpowers i)) = 3) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) = 3 ∧
      Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) ≤ 1 := by
  have hfix : fixedSpace ρ A = U ⊓ fixedSpace ρ (Subgroup.zpowers i) := by
    rw [hA]
    exact (ρ.invariants_comp_sup B _).trans (congrArg (· ⊓ _) hBU)
  refine ⟨hfix ▸ hdint, ?_⟩
  have hBA : B ≤ A := hA ▸ le_sup_left
  have hiA : i ∈ A := (hA ▸ le_sup_right : Subgroup.zpowers i ≤ A)
    (Subgroup.mem_zpowers i)
  have hU : U ≤ fixedSpaceSpan ρ A := by
    rw [← hBU]
    exact (fixedSpace_le_span_of_nontrivial ρ B hB).trans (fixedSpaceSpan_mono ρ hBA)
  have hle := Submodule.finrank_mono (sup_le hU
    (fixedSpace_le_fixedSpaceSpan ρ hiA hi1))
  have hsum := U.finrank_sup_add_finrank_inf_eq (fixedSpace ρ (Subgroup.zpowers i))
  have hquot := (fixedSpaceSpan ρ A).finrank_quotient_add_finrank
  omega

theorem conjugate_module_case (A : Subgroup G) (g : G)
    (hfix : Module.finrank (ZMod 2)
      (fixedSpace ρ (A.map (MulAut.conj g).toMonoidHom)) = 2)
    (hspan : fixedSpaceSpan ρ (A.map (MulAut.conj g).toMonoidHom) = ⊤) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) = 2 ∧ fixedSpaceSpan ρ A = ⊤ := by
  refine ⟨(fixedSpaceConjEquiv ρ A g).finrank_eq.trans hfix, ?_⟩
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  apply (Submodule.map_injective_of_injective e.injective)
  change (fixedSpaceSpan ρ A).map (ρ g) = (⊤ : Submodule (ZMod 2) V).map (ρ g)
  rw [fixedSpaceSpan_map_conj, hspan]
  rw [Submodule.map_top]
  exact (LinearMap.range_eq_top.mpr e.surjective).symm
end MathieuCode.M22ElementaryFour
