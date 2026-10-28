module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.Generation

/-!
# Earlier geometric inputs for the two rank-one branches

This record collects the genuine flag data, F.9.13 kernel and edge facts,
F.9.16 comparison, 13.7.7 noncentrality, and case (2) of 13.8.8 used below.
Every endpoint is constructed from the actual critical pair. The ambient
Sylow subgroup supplies O₂(H)≤L₁T; it is not an extra record field.

The elementary consequences identify containments and nontrivial star
images. Under an endpoint order bound, both star actors have order two.
No generation, small-group recognition or exclusion is a field of the record.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), standing
setup and 13.8.4–11, printed pp.946–950.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
variable {G : Type*} [Group G]
open CriticalGeometry

/-- Earlier local data used by the rank-one deduction. These are flag and
F.9.13/16 facts, 13.7.7 noncentrality, and case (2) of 13.8.8. There is no
rank-one, generation, model-recognition, or exclusion conclusion here. -/
structure Geometry {L H V : Subgroup G} {T : Sylow 2 G} (c : CriticalPair L T H V)
    (V₃ V₁ L₁ : Subgroup G) : Prop where
  seed_le : V₃ ≤ V
  V_le : V ≤ H
  line_le : V₁ ≤ Source.UH H V₃
  line_normalized : H ≤ normalizer (V₁ : Set G)
  line_card : Nat.card V₁ = 2
  Vgamma_le : c.Vgamma ≤ H
  placement : ∃ h : H,
    c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2
  base_edge : (L ⊔ T) ⊓ H = L₁ ⊔ T
  endpoint_core : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2
  DH_kernel : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
    Source.UH H V₃ ⊓ c.Qgamma
  Dgamma_kernel : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
    c.Ugamma V₃ ⊓ Source.QH H
  DH_strict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃
  Dgamma_strict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃
  comparison : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
      (Source.UH H V₃) ≤
    (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)
  core_commutator : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁
  noncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃
  edge_commutator : ⁅edgeGroup L T H c.gamma c.previous,
    V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃

namespace Geometry
variable {L H V V₃ V₁ L₁ : Subgroup G} {T : Sylow 2 G} {c : CriticalPair L T H V}
    (s : Geometry c V₃ V₁ L₁)
include s

/-- The ambient Sylow hypothesis supplies the two-core containment used in lifting. -/
theorem base_core : Source.QH H ≤ L₁ ⊔ T := by
  have hJH : L₁ ⊔ (T : Subgroup G) ≤ H := s.base_edge.symm ▸ inf_le_right
  exact core_le_base_of_sylow T (le_sup_right.trans hJH)

theorem UH_le : Source.UH H V₃ ≤ H := conjugateSpanBy_le_self (s.seed_le.trans s.V_le)
theorem Ugamma_le_Vgamma : c.Ugamma V₃ ≤ c.Vgamma :=
  map_mono (conjugateSpanBy_mono s.seed_le le_rfl)
theorem Ugamma_le : c.Ugamma V₃ ≤ H := s.Ugamma_le_Vgamma.trans s.Vgamma_le
theorem UH_le_endpoint : Source.UH H V₃ ≤ vertexGroup L T H c.gamma :=
  s.endpoint_core.trans ((pCoreIn_le 2 _).trans inf_le_left)
theorem Ugamma_star_ne [Finite G] : Source.starImage H (c.Ugamma V₃) ≠ ⊥ :=
  starImage_ne_bot_of_Dgamma_lt H _ _ _ s.Ugamma_le s.Dgamma_kernel s.Dgamma_strict

/-- In a star image of order at most two, both endpoint actors have order two. -/
theorem actor_cards [Finite G]
    (hc : Nat.card (Source.starImage H c.Vgamma) ≤ 2) :
    Nat.card (Source.starImage H (c.Ugamma V₃)) = 2 ∧
      Nat.card (Source.starImage H c.Vgamma) = 2 := by
  have hle := starImage_mono H s.Ugamma_le_Vgamma
  have hn := ne_bot_of_le_ne_bot s.Ugamma_star_ne hle
  have hV : Nat.card (Source.starImage H c.Vgamma) = 2 := by
    have hp := Nat.card_pos (α := Source.starImage H c.Vgamma)
    have h1 : Nat.card (Source.starImage H c.Vgamma) ≠ 1 := fun h => hn (card_eq_one.mp h)
    omega
  refine ⟨?_, hV⟩
  have hd := card_dvd_of_le hle
  rw [hV] at hd
  exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (fun h => s.Ugamma_star_ne (card_eq_one.mp h))

end Geometry

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
end
