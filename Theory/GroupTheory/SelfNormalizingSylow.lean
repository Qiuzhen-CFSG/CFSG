module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Images of groups with a self-normalizing Sylow subgroup

Frattini's argument shows that a normal subgroup containing a self-normalizing
Sylow subgroup is the whole group. Thus a homomorphism whose Sylow image lies
in a normal subgroup has its entire image there. In A₄ the normal Klein four
contains every two-subgroup, so every such image lies in that Klein four.

Source application: Aschbacher--Smith 10.2.9, printed p.752. This excludes
the odd image in the stabilizer of a positive binary-three natural cover.
-/

public section
open Subgroup
namespace Sylow
variable {H A : Type*} [Group H] [Finite H] [Group A]

/-- Frattini prevents a new image outside a normal subgroup already
containing the image of a self-normalizing Sylow subgroup. -/
theorem range_le_of_self_normalizing {p : ℕ} [Fact p.Prime] (S : Sylow p H)
    (hS : Subgroup.normalizer (S : Set H) = S)
    (f : H →* A) (K : Subgroup A) [K.Normal]
    (hSK : (S : Subgroup H).map f ≤ K) : f.range ≤ K := by
  have hle := map_le_iff_le_comap.mp hSK
  have he := S.normalizer_sup_eq_top' hle
  rw [hS,sup_of_le_right hle] at he
  rintro _ ⟨x,rfl⟩
  exact (show x ∈ K.comap f from he ▸ mem_top x)

/-- An A₄ image of a group with self-normalizing Sylow two-subgroup
is contained in the normal Klein four. -/
theorem image_le_kleinFour_of_self_normalizing (S : Sylow 2 H)
    (hS : Subgroup.normalizer (S : Set H) = S)
    (f : H →* alternatingGroup (Fin 4)) :
    f.range ≤ alternatingGroup.kleinFour (Fin 4) := by
  let K := alternatingGroup.kleinFour (Fin 4)
  let : K.Normal := alternatingGroup.normal_kleinFour (by simp)
  apply S.range_le_of_self_normalizing hS f K
  obtain ⟨R,hR⟩ := (S.isPGroup'.map f).exists_le_sylow
  exact hR.trans_eq (alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by simp) R)
end Sylow
