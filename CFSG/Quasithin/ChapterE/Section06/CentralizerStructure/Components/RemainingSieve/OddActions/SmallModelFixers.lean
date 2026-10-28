module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.ActionBounds
public import Theory.Mathieu.M11.Properties.ElementarySylowFixers
public import Theory.SpecificGroups.PSL3Three.SylowFixers

/-!
# The PSL₃(3) and M₁₁ action bounds in E.6.8

The component's actual Sylow intersection is fixed pointwise by V. Transport
its literal conjugation image through the specified model isomorphism. The
intrinsic pointwise-fixer calculations bound that elementary abelian image
by two, and the automizer–quotient rank identity gives m(V/C_V(L)) ≤ 1.

M₁₁ is used through an actual isomorphism, with no central-cover hypothesis.
For PSL₃(3), the arbitrary-field source predicate is also transported to the
canonical matrix model by the unique finite-field order. Cover elimination,
nontriviality of the action, and the equality U = C_V(L) belong to the parent
odd-alternative assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.8(5),
printed p.248, and 1.1.5(3)(e,f), printed pp.502–503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G}

/-- Transfer an intrinsic elementary fixer bound to the actual ambient action. -/
theorem actionCorank_le_one_of_model_fixers [IsElementaryAbelian 2 V]
    {X : Type*} [Group X] [Finite X] (e : L ≃* X)
    (hbound : ∀ (P : Sylow 2 X) (A : Subgroup (MulAut X)),
      IsElementaryAbelian 2 A → (∀ a ∈ A, ∀ x ∈ P, a x = x) → Nat.card A ≤ 2)
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    actionCorank V L ≤ 1 := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let I := (inducedAutomizer L V).map (Automizer L).subtype
  let J := I.map (MulAut.congr e).toMonoidHom
  let _ := inducedAutomizer_elementary L V hN
  let _ : IsElementaryAbelian 2 I :=
    IsElementaryAbelian.map (A := inducedAutomizer L V) (Automizer L).subtype
  have hJ : IsElementaryAbelian 2 J :=
    IsElementaryAbelian.map (A := I) (MulAut.congr e).toMonoidHom
  have hfixJ : ∀ a ∈ J, ∀ x ∈ P, a x = x := by
    rintro a ⟨b, ⟨c, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ x ⟨y, hy, rfl⟩
    change e (L.normalizerMonoidHom v (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    exact hfix v hv ⟨y, hy⟩
  have hcard : Nat.card (inducedAutomizer L V) ≤ 2 := calc
    Nat.card (inducedAutomizer L V) = Nat.card I :=
      (card_map_of_injective (K := inducedAutomizer L V) (Automizer L).subtype_injective).symm
    _ = Nat.card J := (card_map_of_injective (K := I) (MulAut.congr e).injective).symm
    _ ≤ 2 := hbound P J hJ hfixJ
  rw [actionCorank, ← rank_inducedAutomizer L V hN]
  exact (Nat.log_mono_right hcard).trans (by decide)

variable {K : GroupClass} {T : Sylow 2 G} {M U : Subgroup G}

/-- The M₁₁ component case, using the actual model isomorphism. -/
theorem m11_actionCorank_le_one
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : L ≃* Sporadic.Mathieu.M11) : actionCorank V L ≤ 1 := by
  let _ := h.elementary
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  exact actionCorank_le_one_of_model_fixers e
    (fun P A hA hfix => @Sporadic.Mathieu.m11_elementary_sylow_fixer_card_le_two P A hA hfix)
    (component_normalized h hU hL) S (fun _ hv => component_fixes_sylow S hS hv)

/-- The PSL₃(3) component case, using the actual projective matrix model. -/
theorem psl3Three_actionCorank_le_one
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : L ≃* Matrix.PSL3Three.PSL) : actionCorank V L ≤ 1 := by
  let _ := h.elementary
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  exact actionCorank_le_one_of_model_fixers e
    (fun P A _ hfix => Matrix.PSL3Three.SylowFixers.sylow_fixer_card_le_two P A hfix)
    (component_normalized h hU hL) S (fun _ hv => component_fixes_sylow S hS hv)

/-- The PSL₃(3) bound in the source arbitrary-field model predicate. -/
theorem linear_three_three_actionCorank_le_one
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 3 3) : actionCorank V L ≤ 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF
  let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  exact psl3Three_actionCorank_le_one h hU hL (e.trans (Atlas.fieldEquivPSL 3 eF))

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
