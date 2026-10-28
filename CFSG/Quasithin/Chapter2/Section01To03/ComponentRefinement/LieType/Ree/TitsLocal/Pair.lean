module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.Marking
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.FirstOvergroup
public import Theory.GroupTheory.RelativeNormalizerTransport

/-!
# The Tits pair from intrinsic Sylow stabilizers

The compatible marking is constructed from the actual inner action. If the
two concrete Atlas parabolics are preserved by all automorphisms stabilizing
the marked Sylow subgroup, relative normalizer transport gives an InvariantPair.
The first local overgroup is in M and belongs to He(S).

The two intrinsic automorphism-invariance facts are explicit premises here.
Their verification, the second overgroup's He(S) membership, and its relative
block obstruction remain necessary for the source theorem. This is a
conditional construction for Aschbacher–Smith 2.3.9(7), printed p.526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree
open Subgroup
variable {G : Type*} [Group G] {L A : Subgroup G}

/-- Pull back the actual parabolics with the correct relative invariance. -/
noncomputable def titsPairOfSylowStabilizers
    (e : L ≃* Tits.ParrottGroup)
    (hmark : (A.subgroupOf L).map (titsAtlasEquiv e).toMonoidHom =
      Tits.atlas1600SylowTwoSubgroup)
    (hfirst : ∀ β : MulAut Tits.Atlas1600Group,
      Tits.atlas1600SylowTwoSubgroup.map β.toMonoidHom = Tits.atlas1600SylowTwoSubgroup →
      Tits.ExceptionalParabolics.first.map β.toMonoidHom = Tits.ExceptionalParabolics.first)
    (hsecond : ∀ β : MulAut Tits.Atlas1600Group,
      Tits.atlas1600SylowTwoSubgroup.map β.toMonoidHom = Tits.atlas1600SylowTwoSubgroup →
      Tits.ExceptionalParabolics.second.map β.toMonoidHom = Tits.ExceptionalParabolics.second) :
    InvariantPair L A where
  left := titsFirst e
  right := titsSecond e
  generate := tits_generate e
  invariant_left := normalizes_pullback_of_stabilizer_invariant
    (titsAtlasEquiv e) _ _ hmark hfirst
  invariant_right := normalizes_pullback_of_stabilizer_invariant
    (titsAtlasEquiv e) _ _ hmark hsecond

/-- Construct the marked pair and discharge all first-overgroup obligations.
The intrinsic stabilizer calculations are the only extra inputs to this helper. -/
theorem tits_exists_pair_of_sylow_stabilizers
    {H M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range)
    (hfirst : ∀ β : MulAut Tits.Atlas1600Group,
      Tits.atlas1600SylowTwoSubgroup.map β.toMonoidHom = Tits.atlas1600SylowTwoSubgroup →
      Tits.ExceptionalParabolics.first.map β.toMonoidHom = Tits.ExceptionalParabolics.first)
    (hsecond : ∀ β : MulAut Tits.Atlas1600Group,
      Tits.atlas1600SylowTwoSubgroup.map β.toMonoidHom = Tits.atlas1600SylowTwoSubgroup →
      Tits.ExceptionalParabolics.second.map β.toMonoidHom = Tits.ExceptionalParabolics.second) :
    ∃ (e' : L ≃* Tits.ParrottGroup)
      (d : InvariantPair L ((S : Subgroup H).map H.subtype)),
      d.left = titsFirst e' ∧ d.right = titsSecond e' ∧
      IsConjugationProjection L z ((titsAtlasEquiv e').symm Tits.atlas1600R5) ∧
      (((S : Subgroup H).map H.subtype).subgroupOf L).map
        (titsAtlasEquiv e').toMonoidHom = Tits.atlas1600SylowTwoSubgroup ∧
      d.leftOver ≤ M ∧ d.leftOver ∈ Chapter1.HeOver G
        (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  obtain ⟨e', t, ht, _, himage, hmark⟩ :=
    tits_exists_compatible_sylow_marking h e α hα hinner
  have hproj := tits_projection_of_marked_image e' ht himage
  let d := titsPairOfSylowStabilizers e' hmark hfirst hsecond
  exact ⟨e', d, rfl, rfl, hproj, hmark,
    titsFirstOver_le_of_projection h e' hproj, titsFirstOver_mem_HeOver h e' hproj⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
