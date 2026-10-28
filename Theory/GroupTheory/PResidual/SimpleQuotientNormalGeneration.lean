module
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.Commutator.NormalClosure
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Normal generation over a simple quotient with a two-group kernel

A subgroup with nontrivial image normally generates the simple quotient.
Its normal closure is normalized by the two-group kernel; two-perfection
then lifts full image to the whole original group. The accompanying
commutator-normal-closure theorem lets source applications propagate a
core commutator bound from one selected subgroup to the ambient group.

Source application: Aschbacher–Smith,13.5.15(4), printed p.920.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {X A : Type*} [Group X] [Group A] [IsSimpleGroup A]

theorem normalClosure_eq_top_of_pPerfect_simple_image
    (hX : IsPPerfect 2 X) (f : X→*A) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (K : Subgroup X) (hK : K.map f≠⊥) :
    normalClosure (K:Set X)=⊤ := by
  let N := normalClosure (K:Set X)
  let : (N.map f).Normal := Normal.map inferInstance f hf
  have hi : N.map f=⊤ := by
    rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hz|ht
    · exact (hK (le_bot_iff.mp ((map_mono (show K≤N from le_normalClosure)).trans_eq hz))).elim
    · exact ht
  have htop : IsPPerfect 2 (⊤:Subgroup X) := hX.of_surjective topEquiv.symm.toMonoidHom topEquiv.symm.surjective
  have hn : f.ker≤normalizer (N:Set X) := by rw [normalizer_eq_top];exact le_top
  apply top_unique
  exact isPPerfect_le_of_map_le_of_kernel_normalizes f ⊤ N htop hk hn (by rw [hi];exact le_top)

end Subgroup
end
