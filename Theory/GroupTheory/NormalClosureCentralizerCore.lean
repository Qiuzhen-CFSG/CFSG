module

public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Centralizers of normal closures of Sylow-central subgroups

If `C_G(Z)` is a Sylow `p`-subgroup, then the centralizer of the normal
closure of `Z` is exactly `O_p(G)`. The centralizer is a normal `p`-subgroup,
giving one inclusion. Conversely, the normal `p`-core centralizes `Z`, hence
all its conjugates.

This is the elementary centralizer step in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 15.4.11(1), combined
manuscript (1 March 2004), printed p. 1160. No solvability assumption is
needed for this step.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Centralizers inside a subgroup, transported to the ambient group. -/
public theorem map_centralizer_subtype (M : Subgroup G) (V : Subgroup M) :
    (centralizer (V : Set M)).map M.subtype =
      M ⊓ centralizer (V.map M.subtype : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (hy v hv)
  · rintro ⟨hx, hc⟩
    refine mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    intro v hv
    apply Subtype.ext
    exact hc v (mem_map.mpr ⟨v, hv, rfl⟩)

/-- If `C_G(Z)` is a `p`-group containing the `p`-core, taking the normal
closure of `Z` cuts its centralizer down to the `p`-core. -/
public theorem centralizer_normalClosure_eq_pCore_of_isPGroup
    (p : ℕ) (Z : Subgroup G)
    (hC : IsPGroup p (centralizer (Z : Set G)))
    (hcore : pCore p G ≤ centralizer (Z : Set G)) :
    centralizer (normalClosure (Z : Set G) : Set G) = pCore p G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hC.to_le (centralizer_le le_normalClosure)⟩
  · apply le_centralizer_iff.mp
    exact normalClosure_le_normal (le_centralizer_iff.mpr hcore)

/-- A Sylow centralizer becomes the `p`-core after normal closure. -/
public theorem centralizer_normalClosure_eq_pCore_of_eq_sylow
    {p : ℕ} (P : Sylow p G) (Z : Subgroup G)
    (hC : centralizer (Z : Set G) = (P : Subgroup G)) :
    centralizer (normalClosure (Z : Set G) : Set G) = pCore p G := by
  apply centralizer_normalClosure_eq_pCore_of_isPGroup
  · rw [hC]
    exact P.isPGroup'
  · rw [hC]
    exact pCore_isPGroup.le_sylow_of_normal P

end Subgroup
