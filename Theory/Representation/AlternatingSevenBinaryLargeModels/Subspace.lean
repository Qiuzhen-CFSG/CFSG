module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Representations in coordinates of an invariant subspace

An embedding with a left inverse transports an ambient action to coordinates
once its image is invariant. For permutation groups, it suffices to check the
adjacent transpositions. The construction keeps the actual group action and
requires no presentation or comparison inferred from group orders.
-/

@[expose] public section

namespace Representation.AlternatingSevenBinaryLargeModels

variable {K G V W : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Transport an action onto the coordinates of an invariant embedded space. -/
def onSubspace (ρ : Representation K G V) (E : W →ₗ[K] V) (L : V →ₗ[K] W)
    (hLE : L.comp E = LinearMap.id)
    (hInv : ∀ g, E.comp (L.comp ((ρ g).comp E)) = (ρ g).comp E) :
    Representation K G W where
  toFun g := L.comp ((ρ g).comp E)
  map_one' := by simp only [map_one, Module.End.one_eq_id, LinearMap.id_comp]; exact hLE
  map_mul' g h := by
    ext v
    have hv := LinearMap.congr_fun (hInv h) v
    change E (L (ρ h (E v))) = ρ h (E v) at hv
    change L (ρ (g * h) (E v)) = L (ρ g (E (L (ρ h (E v)))))
    rw [map_mul]
    change L (ρ g (ρ h (E v))) = _
    rw [hv]

/-- Invariance under adjacent transpositions gives invariance under every permutation. -/
theorem invariant_of_adjacent {n : ℕ}
    (ρ : Representation K (Equiv.Perm (Fin (n + 1))) V)
    (E : W →ₗ[K] V) (L : V →ₗ[K] W)
    (hLE : L.comp E = LinearMap.id)
    (h : ∀ i : Fin n,
      E.comp (L.comp ((ρ (Equiv.swap i.castSucc i.succ)).comp E)) =
        (ρ (Equiv.swap i.castSucc i.succ)).comp E) :
    ∀ g, E.comp (L.comp ((ρ g).comp E)) = (ρ g).comp E := by
  let S : Submonoid (Equiv.Perm (Fin (n + 1))) := {
    carrier := {g | E.comp (L.comp ((ρ g).comp E)) = (ρ g).comp E}
    one_mem' := by
      simp only [Set.mem_ofPred_eq, map_one, Module.End.one_eq_id,
        LinearMap.id_comp, hLE, LinearMap.comp_id]
    mul_mem' := by
      intro g h hg hh
      simp only [Set.mem_ofPred_eq] at hg hh ⊢
      ext v
      have hgv := LinearMap.congr_fun hg (L (ρ h (E v)))
      have hhv := LinearMap.congr_fun hh v
      simp only [LinearMap.comp_apply] at hgv hhv
      simpa only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hhv] using hgv }
  have htop : S = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ n]
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  intro g
  exact (show g ∈ S by rw [htop]; trivial)

end Representation.AlternatingSevenBinaryLargeModels
