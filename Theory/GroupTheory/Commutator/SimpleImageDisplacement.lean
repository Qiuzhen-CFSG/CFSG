module
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Displacement transfer through a simple image

A subgroup with nontrivial image normally generates a simple quotient.
When the kernel is a two-group, every two-perfect subgroup lies in that
normal closure. A commutator bound with a normal subgroup, modulo another
normal subgroup, consequently extends to every two-perfect subgroup.
No complement or centrality of the kernel is required.

Source application: Aschbacher--Smith, the paragraph preceding 12.2.24,
printed p.804.
-/

public section
namespace Subgroup
/-- A displacement bound extends from a nontrivial simple image to every
p-perfect subgroup, without choosing any complement to the kernel. -/
theorem commutator_le_of_pPerfect_simple_image
    {J B : Type*} [Group J] [Group B] [IsSimpleGroup B]
    (a : J →* B) (ha : Function.Surjective a) (hk : IsPGroup 2 a.ker)
    (Q Z X E : Subgroup J) [Q.Normal] [Z.Normal]
    (hX : IsPPerfect 2 X) (hE : E.map a ≠ ⊥)
    (hd : ⁅Q,E⁆ ≤ Z) : ⁅Q,X⁆ ≤ Z := by
  let N := normalClosure (E : Set J)
  let : (N.map a).Normal := Normal.map inferInstance a ha
  have hn : N.map a = ⊤ := by
    rcases (inferInstance : (N.map a).Normal).eq_bot_or_eq_top with he | ht
    · exact (hE (le_bot_iff.mp ((map_mono (show E ≤ N from le_normalClosure)).trans_eq he))).elim
    · exact ht
  have hXN : X ≤ N := isPPerfect_le_of_map_le_of_kernel_normalizes a X N hX hk
    (by rw [normalizer_eq_top]; exact le_top) (by rw [hn]; exact le_top)
  exact (commutator_mono le_rfl hXN).trans
    (commutator_normalClosure_le_of_normal Q E Z hd)


end Subgroup
