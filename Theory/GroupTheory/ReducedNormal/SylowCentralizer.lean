module

public import Theory.GroupTheory.ReducedNormal.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Enlarging a reduced normal subgroup using a Sylow centralizer

Let V ≤ W be normal elementary abelian p-subgroups, with V reduced.
If the elements of a fixed Sylow subgroup centralizing V also centralize W,
then W is reduced. The core of G/C_G(W) lies in the image Sylow. Its lift
centralizes V by reducedness, and hence centralizes W by the Sylow condition.

This supplies the omega-center step in Aschbacher–Smith, Lemma 3.2.13,
printed pp.584–585, without an additional odd-kernel extension theorem.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An elementary normal overgroup of a reduced subgroup is reduced when
its Sylow centralizer contains that of the smaller subgroup. -/
theorem IsPReduced.of_le_of_sylow_centralizer_le
    {V W : Subgroup G} (hV : IsPReduced p V) [W.Normal]
    [IsElementaryAbelian p W] (S : Sylow p G) (hVW : V ≤ W)
    (hC : (S : Subgroup G) ⊓ centralizer (V : Set G) ≤ centralizer (W : Set G)) :
    IsPReduced p W := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective C)
  apply bot_unique
  intro z hz
  have hs : z ∈ (Sbar : Subgroup (G ⧸ C)) :=
    pCore_isPGroup.le_sylow_of_normal Sbar hz
  change z ∈ (S : Subgroup G).map q at hs
  obtain ⟨s, hs, rfl⟩ := hs
  exact (QuotientGroup.eq_one_iff s).mpr
    (hC ⟨hs, hV.quotient_core_preimage_le_centralizer hVW hz⟩)

end Theory.GroupTheory
