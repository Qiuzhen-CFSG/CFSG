module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BinaryAction
public import Theory.SpecificGroups.AlternatingSix.SylowPointwiseTwoPower.Rank

/-!
# Binary symplectic component action coranks

Transport the actual induced action through Sp₄(2)′ ≃ A₆. Its image is
a two-group fixing the specified Sylow subgroup pointwise, so the marked
Aut(A₆) calculation bounds its order by four. The automizer–quotient rank
identity turns this into a corank bound. Escape from M excludes corank zero.

Both positive coranks remain possible at this stage. Identifying the Borel
or parabolic and constructing a root or escaping intermediate subgroup are
separate obligations; the bound alone is not the binary E.6.8 alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(2),
printed pp.247–248 (PDF pp.258–259).
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G}

/-- The actual action image has order at most four, including its possible
outer actors on the binary derived group. -/
theorem binary_action_image_card_le_four [IsElementaryAbelian 2 V]
    (hm : SymplecticDerivedModel L 1) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    Nat.card (inducedAutomizer L V) ≤ 4 := by
  obtain ⟨e⟩ := alternating_six_of_model_one hm
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let I := (inducedAutomizer L V).map (Automizer L).subtype
  let J := I.map (MulAut.congr e).toMonoidHom
  have hI : IsPGroup 2 (inducedAutomizer L V) := by
    exact (IsElementaryAbelian.isPGroup 2 V).comap_subtype.map _
  have hJ : IsPGroup 2 J := (hI.map _).map _
  have hfixJ : ∀ a ∈ J, ∀ x ∈ (P : Subgroup (alternatingGroup (Fin 6))), a x = x := by
    rintro a ⟨b, ⟨c, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ x ⟨y, hy, rfl⟩
    change e (L.normalizerMonoidHom v (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    exact hfix v hv ⟨y, hy⟩
  calc
    Nat.card (inducedAutomizer L V) = Nat.card I :=
      (card_map_of_injective (Automizer L).subtype_injective).symm
    _ = Nat.card J := (card_map_of_injective (MulAut.congr e).injective).symm
    _ ≤ 4 := AlternatingSix.ShadowLocal.twoSubgroup_fixes_sylow_card_le_four P J hJ hfixJ

/-- The induced image bound controls the literal quotient V/C_V(L). -/
theorem binary_actionCorank_le_two [IsElementaryAbelian 2 V]
    (hm : SymplecticDerivedModel L 1) (hN : V ≤ normalizer (L : Set G))
    (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    actionCorank V L ≤ 2 := by
  rw [actionCorank, ← rank_inducedAutomizer L V hN]
  exact (Nat.log_mono_right (binary_action_image_card_le_four hm S hfix)).trans (by decide)

variable {K : GroupClass} {T : Sylow 2 G} {M U : Subgroup G}

/-- Escape and the genuine Sylow action leave precisely coranks one and two. -/
theorem component_binary_actionCorank_cases (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) :
    actionCorank V L = 1 ∨ actionCorank V L = 2 := by
  let _ := h.elementary
  obtain ⟨hN, S, _, hfix⟩ := component_sylow_action h hU hL rfl
  have hbound := binary_actionCorank_le_two hm hN S hfix
  have hpos : 0 < actionCorank V L :=
    fixedSpace_corank_pos h (component_not_le h earlier hU hL)
  omega

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
