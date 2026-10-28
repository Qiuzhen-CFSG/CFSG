module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Centralizers modulo a normal subgroup

The subgroup `centralizerModulo T A N` consists of the elements of `T` whose
images centralize the image of `A` in `G/N`. Membership is equivalent to all
commutators with `A` lying in `N`. This gives monotonicity in the kernel and
allows replacing the kernel by its intersection with `T` when `A ≤ T`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Definition E.1.1 and the argument for Lemma E.1.8(3), pp.209--211.
-/

@[expose] public section
namespace Subgroup
variable {G : Type*} [Group G]
open scoped commutatorElement IsMulCommutative

/-- The inverse image in `T` of the centralizer of the image of `A` in `G/N`. -/
def centralizerModulo (T A N : Subgroup G) [N.Normal] : Subgroup G :=
  T ⊓ (centralizer (A.map (QuotientGroup.mk' N) : Set (G ⧸ N))).comap
    (QuotientGroup.mk' N)

theorem mem_centralizerModulo_iff {T A N : Subgroup G} [N.Normal] {x : G} :
    x ∈ centralizerModulo T A N ↔ x ∈ T ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ N := by
  change (x ∈ T ∧ _) ↔ _
  apply and_congr_right
  intro _
  constructor
  · intro hx a ha
    have hc := (mem_centralizer_iff.mp hx) _ (mem_map_of_mem _ ha)
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' N) ⁅a, x⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc
  · intro hx
    apply mem_centralizer_iff.mpr
    rintro _ ⟨a, ha, rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hx a ha)

theorem centralizerModulo_le (T A N : Subgroup G) [N.Normal] :
    centralizerModulo T A N ≤ T := inf_le_left

theorem centralizerModulo_mono_kernel {T A N M : Subgroup G} [N.Normal] [M.Normal]
    (h : N ≤ M) : centralizerModulo T A N ≤ centralizerModulo T A M := by
  intro x hx
  obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx
  exact mem_centralizerModulo_iff.mpr ⟨hxT, fun a ha => h (hc a ha)⟩

theorem inf_le_centralizerModulo (T A N : Subgroup G) [N.Normal] :
    T ⊓ N ≤ centralizerModulo T A N := by
  intro x hx
  apply mem_centralizerModulo_iff.mpr
  exact ⟨hx.1, fun a ha => commutator_le_right A N
    (commutator_mem_commutator ha hx.2)⟩

/-- Abelian subgroups centralize their own image in every quotient. -/
theorem le_centralizerModulo_of_isMulCommutative {T A N : Subgroup G} [N.Normal]
    [IsMulCommutative A] (hAT : A ≤ T) : A ≤ centralizerModulo T A N := by
  intro x hx
  apply mem_centralizerModulo_iff.mpr
  refine ⟨hAT hx, fun a ha => ?_⟩
  have hc : a * x = x * a := congrArg Subtype.val
    (mul_comm (⟨a, ha⟩ : A) (⟨x, hx⟩ : A))
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
  exact N.one_mem

/-- Only `T ∩ N` matters when both entries of the commutator lie in `T`. -/
theorem centralizerModulo_eq_of_inf_eq {T A N M : Subgroup G} [N.Normal] [M.Normal]
    (hAT : A ≤ T) (h : T ⊓ N = T ⊓ M) :
    centralizerModulo T A N = centralizerModulo T A M := by
  ext x
  simp only [mem_centralizerModulo_iff]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun a ha => ?_⟩
    have ht : ⁅a, x⁆ ∈ T := T.mul_mem
      (T.mul_mem (T.mul_mem (hAT ha) hx) (T.inv_mem (hAT ha))) (T.inv_mem hx)
    exact (show ⁅a, x⁆ ∈ T ⊓ M from h ▸ ⟨ht, hc a ha⟩).2
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun a ha => ?_⟩
    have ht : ⁅a, x⁆ ∈ T := T.mul_mem
      (T.mul_mem (T.mul_mem (hAT ha) hx) (T.inv_mem (hAT ha))) (T.inv_mem hx)
    exact (show ⁅a, x⁆ ∈ T ⊓ N from h.symm ▸ ⟨ht, hc a ha⟩).2

end Subgroup
