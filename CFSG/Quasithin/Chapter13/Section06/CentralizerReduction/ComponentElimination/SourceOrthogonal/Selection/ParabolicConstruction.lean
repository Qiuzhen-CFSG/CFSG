module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Replacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction

/-!
# Geometric construction for the source rank-four selection

The actual source subgroup Lᵥ(Tᵥ ∩ K) is now identified with a minimal
parabolic of the prescribed binary linear model. The construction includes
the full-flag marking of the actual Sylow intersection and proves the
index-three premise from the earlier cubic quotient and movement of z.
The adjacent-node parabolic supplies a moving perfect residual in the
inner-action branch. Its local-family membership, star-quasisimplicity and
own SL₃(2) plus model give the contradiction to 13.6.22. Movement of z is
transported through the original plus map, without assuming Lᵥ is contained
in the residual before quotienting. The resulting outside actor forces
dimension four and the middle node.

The final consumer accepts the reduced SL₄(2)/SL₅(2) alternative and
constructs the actual SL₄(2) model and middle-node marking. Only the genuine
earlier source inputs remain explicit: 13.6.2–16, Lᵥ-containment from
13.6.20, and the reduced model list and universal small-model exclusion.
Their discharge remains with the component-elimination owner. The intrinsic
quotient comparison and ambient residual equality in 13.6.23(1) remain with
the source-selection owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.6.23(2–3), printed p.933/PDF p.950, using the argument on p.932.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
open ComponentSelection BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- The geometric part of the source selection, under the prescribed linear
model. Both the marking and the outside actor are constructed; neither is
an input. Dimension four and the middle node refer to this same model. -/
theorem middle_node_of_source_linear_model
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (h16 : ∀ A ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (A : Set G) → ¬ A ≤ centralizer ({z} : Set G) →
      ⁅A, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = A)
    (hR : ∀ A ∈ Yz L T z v, pCore 2 (Gplus A L T z v hL hz) = ⊥)
    (hsmall : ∀ A ∈ Yz L T z v,
      ¬ Nonempty (plusImage A L T z v hL hz A ≃* SL(3, ZMod 2)))
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2)) :
    (¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) ∧
      ∃ (b : Basis m) (i : Fin m), m = 3 ∧ i.val = 1 ∧
        ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
          (plusImage K L T z v hL hz K)).map
          (e.trans (slEquivLinear (m + 1))).toMonoidHom = minimalParabolic b i := by
  have hout := InnerAction.outside_actor_of_source_linear_model K L T z v hL hz
    hY hLK hK hc hmove h16 hR hsmall hm e
  exact ⟨hout, middle_node_of_outside_actor K L T z v hL hz hY.1 hLK hK hc hmove
    (hR K hY) hm e hout⟩

/-- Apply the geometric selection to the reduced source model list. This
supplies the actual rank-four plus model needed by the intrinsic-quotient
assembly, together with the literal middle-node parabolic for that model. -/
theorem exists_rankFour_sourceParabolic
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (h16 : ∀ A ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (A : Set G) → ¬ A ≤ centralizer ({z} : Set G) →
      ⁅A, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = A)
    (hR : ∀ A ∈ Yz L T z v, pCore 2 (Gplus A L T z v hL hz) = ⊥)
    (hsmall : ∀ A ∈ Yz L T z v,
      ¬ Nonempty (plusImage A L T z v hL hz A ≃* SL(3, ZMod 2)))
    (hmodels : Nonempty (plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) ∨
      Nonempty (plusImage K L T z v hL hz K ≃* SL(5, ZMod 2))) :
    ∃ (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) (b : Basis 3),
      (¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) ∧
      ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
        (plusImage K L T z v hL hz K)).map
        (e.trans (slEquivLinear 4)).toMonoidHom = minimalParabolic b (1 : Fin 3) := by
  rcases hmodels with hfour | hfive
  · obtain ⟨e⟩ := hfour
    obtain ⟨hout, b, i, _, hi, hP⟩ := middle_node_of_source_linear_model
      K L T z v hL hz hY hLK hK hc hmove h16 hR hsmall (m := 3) (Or.inl rfl) e
    have hi' : i = (1 : Fin 3) := Fin.ext hi
    exact ⟨e, b, hout, hi' ▸ hP⟩
  · obtain ⟨e⟩ := hfive
    obtain ⟨_, _, _, hm, _⟩ := middle_node_of_source_linear_model
      K L T z v hL hz hY hLK hK hc hmove h16 hR hsmall (m := 4) (Or.inr rfl) e
    exact (by omega : False).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
