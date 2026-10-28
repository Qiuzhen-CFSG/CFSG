module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Carrier
public import Theory.SpecificGroups.SymplecticFour.Binary.DerivedSylowAction

/-!
# The actual binary component action in E.6.8(2)

The subgroup V fixes the component's Sylow two-subgroup pointwise. In the
binary derived model, transport to the marked A₆ Sylow calculation places
every such involutory actor in the permutation action of S₆. The polar
equivalence then realizes that action by matrices in the full Sp₄(2).
The conjugating matrices need not belong to Sp₄(2)′.

This proves action-image containment only; selecting a root subgroup and
identifying L ∩ M remain separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(2),
printed pp.247–248, and the Sylow action calculation of 16.1.6, p.1172.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G}

/-- The binary Sylow action is induced by the full symplectic group on its
derived subgroup. This retains possible outer automorphisms of A₆. -/
theorem binary_action_le_full_conjugation [IsElementaryAbelian 2 V]
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : L ≃* commutator (Sp F)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    (((inducedAutomizer L V).map (Automizer L).subtype).map
      (MulAut.congr e).toMonoidHom) ≤
      (MulAut.conjNormal (H := commutator (Sp F))).range := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  rintro a ⟨b, ⟨c, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
  have hv2 : v ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) (v : G) hv
  have hp : (MulAut.congr e (L.normalizerMonoidHom v)) ^ (2 ^ 1) = 1 := by
    change (MulAut.congr e (L.normalizerMonoidHom v)) ^ 2 = 1
    rw [← map_pow, ← map_pow, hv2, map_one, map_one]
  have hf : ∀ x ∈ (Q : Subgroup (commutator (Sp F))),
      MulAut.congr e (L.normalizerMonoidHom v) x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change e (L.normalizerMonoidHom v (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    exact hfix v hv ⟨x, hx⟩
  obtain ⟨σ, hσ⟩ := Binary.derived_twoPower_fixes_sylow hF Q _ hp hf
  let g := (Binary.fieldEquivSp (Binary.fieldEquivZModTwo F hF)).symm
    (Binary.symmetricSixEquiv σ)
  refine ⟨g, ?_⟩
  change MulAut.conjNormal g = MulAut.congr e (L.normalizerMonoidHom v)
  rw [← hσ]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact (Binary.derivedPermutationAction_matrix hF σ x).symm

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Realize the source component action in the fixed binary matrix model,
using the actual Sylow subgroup supplied by the local hypotheses. -/
theorem component_binary_action (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) :
    ∃ e : L ≃* commutator (Sp (ZMod 2)),
      (((inducedAutomizer L V).map (Automizer L).subtype).map
        (MulAut.congr e).toMonoidHom) ≤
        (MulAut.conjNormal (H := commutator (Sp (ZMod 2)))).range := by
  let _ := h.elementary
  obtain ⟨_, F, _, _, hcard, ⟨e⟩⟩ := hm
  have hF : Nat.card F = 2 := by simpa using hcard
  let f := Binary.fieldEquivSp (Binary.fieldEquivZModTwo F hF)
  let d : commutator (Sp F) ≃* commutator (Sp (ZMod 2)) :=
    (f.subgroupMap _).trans (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective]
      rfl))
  obtain ⟨_, S, _, hfix⟩ := component_sylow_action h hU hL rfl
  exact ⟨e.trans d, binary_action_le_full_conjugation (by simp) (e.trans d) S hfix⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
