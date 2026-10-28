module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Prime-core images under central core comparison

For a surjection A → B whose induced map A/Oₚ(A) → B/Oₚ(B) has central
kernel, the inverse image of Oₚ(B) commutes with A modulo Oₚ(A).
Mapping this commutator to B puts [Oₚ(B),B] in the image of Oₚ(A).
In particular the cores map onto one another when [Oₚ(B),B] = Oₚ(B).
No prime-group hypothesis on the original kernel is required.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.19, printed p.931, for the affine plus images of parabolic residuals.
-/

public section
open Subgroup
namespace MonoidHom
variable {A B : Type*} [Group A] [Group B] {p : ℕ}

/-- Centrality after removing the prime cores makes the target core
commutator lift into the image of the source core. -/
theorem commutator_pCore_le_map_of_central_coreMap (f : A →* B) (hf : Function.Surjective f)
    (hc : pCore p A ≤ (pCore p B).comap f)
    (hk : (QuotientGroup.map (pCore p A) (pCore p B) f hc).ker ≤
      center (A ⧸ pCore p A)) :
    ⁅pCore p B, (⊤ : Subgroup B)⁆ ≤ (pCore p A).map f := by
  let q := QuotientGroup.mk' (pCore p A)
  have hcentral : ((pCore p B).comap f).map q ≤ center (A ⧸ pCore p A) := by
    simpa only [QuotientGroup.ker_map] using hk
  have hcomm : ⁅(pCore p B).comap f, (⊤ : Subgroup A)⁆ ≤ pCore p A := by
    have hz := commutator_top_right_eq_bot_iff_le_center.mpr hcentral
    rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective _),
      ← map_commutator] at hz
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  have hm := map_mono (f := f) hcomm
  rwa [map_commutator, map_comap_eq_self_of_surjective hf,
    map_top_of_surjective f hf] at hm

/-- If the target acts onto its prime core by commutators, the source core
maps onto that core despite possible central elements of other orders. -/
theorem map_pCore_eq_of_central_coreMap (f : A →* B) (hf : Function.Surjective f)
    (hc : pCore p A ≤ (pCore p B).comap f)
    (hk : (QuotientGroup.map (pCore p A) (pCore p B) f hc).ker ≤
      center (A ⧸ pCore p A))
    (hcomm : ⁅pCore p B, (⊤ : Subgroup B)⁆ = pCore p B) :
    (pCore p A).map f = pCore p B := by
  apply le_antisymm (map_le_iff_le_comap.mpr hc)
  rw [← hcomm]
  exact f.commutator_pCore_le_map_of_central_coreMap hf hc hk

end MonoidHom
