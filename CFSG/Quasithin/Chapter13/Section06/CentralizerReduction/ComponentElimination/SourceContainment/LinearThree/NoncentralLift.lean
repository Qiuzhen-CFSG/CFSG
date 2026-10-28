module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.ParabolicProjection
public import Theory.GroupTheory.PResidual.EquivariantProjection

/-!
# Lifting the noncentral projection with its own kernel

The actual component Sylow image generates the projected Lᵥ by commutators.
The projection has two-group kernel on Lᵥ, by its earlier cubic core
quotient. If Lᵥ normalizes the original K, these commutators lie in Lᵥ ∩ K.
The generic equivariant projection lemma then removes the two-group
kernel and proves Lᵥ ≤ K.

Normalization of K by Lᵥ remains a source obligation. In particular this
module neither assumes nor deduces that the entire plus-map kernel is a
two-group or lies inside K. All maps are the original source maps.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
paragraph of the proof of 13.6.20, printed p.931.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- The noncentral projection lifts using only its own two-group kernel.
The remaining source obligation is normalization of the original K by L_v. -/
theorem lv_le_of_noncentral_of_normalizes (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hcomm : ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥)
    (hLK : Lv L v ≤ normalizer (K : Set G)) : Lv L v ≤ K := by
  obtain ⟨f, hf, hne, _, hk, _⟩ := exists_noncentral_projection K L T z v hL hz hK hn e hc hcomm
  have hgen := (projection_parabolic_and_commutator K L T z v hL hz hK hn e f hf hc hne).2.2.2
  apply le_of_equivariant_projection (Lv L v) K (Tv T v ⊓ K)
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v))
    (inf_le_left.trans hL) inf_le_right hLK f (componentSylowMap K L T z v hL hz)
    (pCore_isPGroup.to_le hk) _ hgen
  intro s l
  apply Subtype.ext
  exact projection_equivariant K L T z v hL hz hK hn e f hf ⟨s, s.property.1⟩ l

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
