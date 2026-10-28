module
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Stellmacher.OmegaOneCenterMap

/-!
# Detecting fixed vectors in the Sylow omega-center

If a Sylow two-group normalizes an elementary subgroup W and an actor L,
then C_W(L) is also normalized. When it is nontrivial, the p-group center
lemma supplies a nonidentity element of C_W(L) in Ω₁(Z(T)). Consequently
C_{Ω₁(Z(T))}(L)=1 implies C_W(L)=1.

This is the elementary fixed-space step in Aschbacher--Smith 5.1.19,
printed pp.643--644, following 5.1.14(3).
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Sylow-central disjointness eliminates the entire fixed subgroup. -/
theorem inf_centralizer_eq_bot_of_omega_disjoint
    (T : Sylow 2 G) (L W : Subgroup G) (hW : IsElementaryAbelian 2 W)
    (hWT : W ≤ (T : Subgroup G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) = ⊥) : W ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hn
  have hnorm : (T : Subgroup G) ≤ normalizer
      (W ⊓ centralizer (L : Set G) : Set G) :=
    (le_inf hTW (hTL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨z, hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hn (inf_le_left.trans hWT) hnorm)
  have hzW : (z : G) ∈ W := z.property.1.1
  have hzΩ : (z : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    let := hW
    exact ⟨hWT hzW, elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzW,
      z.property.2.2⟩
  have hz : (z : G) ∈ (⊥ : Subgroup G) := hZ ▸ ⟨hzΩ, z.property.1.2⟩
  exact hz1 (Subtype.ext (mem_bot.mp hz))
end Subgroup
