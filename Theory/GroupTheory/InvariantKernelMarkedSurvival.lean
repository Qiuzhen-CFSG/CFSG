module
public import Theory.GroupTheory.RankOneInvariantKernelQuotient
public import Theory.GroupTheory.SubgroupTransport.Restriction
public import Mathlib.GroupTheory.Nilpotent

/-!
# Marked survival in the reduced pushing-up quotient

The largest ambient-normal subgroup fixed by a Sylow automorphism is also
fixed by its literal conjugacy twist. An iterate escaping the intersection
of the two Sylows therefore cannot start in this kernel. A marked subgroup
of the third lower-central term which survives a quotient forces the actual
image subgroup to retain class three.

These are the kernel and class-preservation steps of Niles, *Pushing-up in
finite groups* (1979), Lemmas 6.4–6.5, printed pp.53–54. The escape calculation
from the intersection diagram is a separate input to the kernel criterion.
-/

public section
open Subgroup NilesRankOneKernel Theory.GroupTheory.SubgroupTransport
namespace Theory.GroupTheory
variable {H : Type*} [Group H]

/-- The maximal ambient-normal beta-invariant kernel is fixed by the literal
conjugacy twist of beta. -/
theorem invariantKernel_twisted_image (S : Subgroup H) (β : MulAut S) (g : H) :
    image (β.trans ((MulAut.conj g).subgroupMap S))
      ((invariantNormalKernel S β).map S.subtype) =
      (invariantNormalKernel S β).map S.subtype := by
  let N := invariantNormalKernel S β
  change ((N.map S.subtype).comap S.subtype).map
    (ambientHom (β.trans ((MulAut.conj g).subgroupMap S))) = N.map S.subtype
  rw [comap_map_eq_self_of_injective S.subtype_injective]
  have hh : ambientHom (β.trans ((MulAut.conj g).subgroupMap S)) =
      (MulAut.conj g).toMonoidHom.comp (S.subtype.comp β.toMonoidHom) := rfl
  rw [hh, ← map_map, ← map_map, invariantNormalKernel_fixed]
  exact Normal.map_conj_eq _ g

/-- The same kernel lies in both members of the actual conjugate pair. -/
theorem invariantKernel_le_twisted_intersection (S : Subgroup H) (β : MulAut S) (g : H) :
    (invariantNormalKernel S β).map S.subtype ≤
      S ⊓ S.map (MulAut.conj g).toMonoidHom := by
  refine le_inf (map_subtype_le _) ?_
  rw [← invariantKernel_twisted_image S β g]
  exact image_le _ _

/-- An escaping iterate of a marked subgroup cannot lie in the invariant
kernel. The iteration is through the literal partial subgroup transport. -/
theorem not_le_invariantKernel_of_twisted_escape
    (S : Subgroup H) (β : MulAut S) (g : H) (Z : Subgroup H) (n : ℕ)
    (hescape : ¬ (image (β.trans ((MulAut.conj g).subgroupMap S)))^[n] Z ≤
      S ⊓ S.map (MulAut.conj g).toMonoidHom) :
    ¬ Z ≤ (invariantNormalKernel S β).map S.subtype := by
  intro hZ
  have hi : ∀ k, (image (β.trans ((MulAut.conj g).subgroupMap S)))^[k] Z ≤
      (invariantNormalKernel S β).map S.subtype := by
    intro k
    induction k with
    | zero => exact hZ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (image_mono _ ih).trans_eq (invariantKernel_twisted_image S β g)
  exact hescape ((hi n).trans (invariantKernel_le_twisted_intersection S β g))

/-- A surviving marked third commutator preserves exact class three in the
actual image subgroup of a quotient map. -/
theorem nilpotencyClass_image_eq_three_of_surviving_subgroup
    {J : Type*} [Group J] (f : H →* J) (T Z : Subgroup H)
    (hclass : T.lowerCentralSeries 3 = ⊥)
    (hZ : Z ≤ T.lowerCentralSeries 2) (hsurvive : ¬ Z ≤ f.ker) :
    Group.nilpotencyClass (T.map f) = 3 := by
  have h3 : (T.map f).lowerCentralSeries 3 = ⊥ := by
    rw [← map_lowerCentralSeries, hclass, Subgroup.map_bot]
  have h2 : (T.map f).lowerCentralSeries 2 ≠ ⊥ := by
    intro hh
    apply hsurvive
    apply (Subgroup.map_eq_bot_iff _).mp
    apply le_bot_iff.mp
    exact (map_mono hZ).trans_eq ((map_lowerCentralSeries T f 2).trans hh)
  have htop3 : (⊤ : Subgroup (T.map f)).lowerCentralSeries 3 = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ (T.map f).subtype_injective).mp
    rw [top_subtype_lowerCentralSeries, h3]
  have htop2 : (⊤ : Subgroup (T.map f)).lowerCentralSeries 2 ≠ ⊥ := by
    intro hh
    apply h2
    rw [← top_subtype_lowerCentralSeries, hh, Subgroup.map_bot]
  let : Group.IsNilpotent (T.map f) := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨3, htop3⟩
  have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp htop3
  have hgt : ¬ Group.nilpotencyClass (T.map f) ≤ 2 := fun h =>
    htop2 (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h)
  omega

end Theory.GroupTheory
