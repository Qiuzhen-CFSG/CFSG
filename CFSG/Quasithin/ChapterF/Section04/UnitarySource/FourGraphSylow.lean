module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourGraph
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraphSylow
public import Theory.GroupTheory.SaturatedCentralizer

/-!
# Saturated graph involutions and the orders of their fixed local Sylows

Choose a graph involution in the specified Sylow of the whole middle.
Conjugating inside that same middle saturates its centralizer there;
the conjugation simultaneously transports both fixed endpoint maps and
the marked central graph generator. The native symplectic Sylow counts
then give 2q⁴ for all three fixed groups, with either endpoint orientation.
This supplies the local Sylow data needed before the ambient F.4.37
promotion. It does not identify the source Sylow with the full ambient T.

Source: Aschbacher–Smith F.4.37(1–4), printed p.293 of
`refs/quasithin.pdf`. The ambient normalizer argument in part (4) remains
separate from these native and whole-middle transport statements.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourGraph
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable (m : ℕ) (hm : 1 ≤ m)

private theorem saturated_sylow {B : Type*} [Group B] [Finite B]
    (U : Sylow 2 B) (b : U) :
    ∃ c : B, c*b.val*c⁻¹ ∈ (U : Subgroup B) ∧
      ∃ P : Sylow 2 (centralizer ({c*b.val*c⁻¹} : Set B)),
        (P : Subgroup _).map (centralizer ({c*b.val*c⁻¹} : Set B)).subtype =
          (U : Subgroup B) ⊓ centralizer ({c*b.val*c⁻¹} : Set B) := by
  obtain ⟨t,ht,hmax⟩ := U.exists_conjugate_with_saturated_centralizer b
  obtain ⟨c,hc⟩ := isConj_iff.mp ht
  rw [map_subtype_centralizer_singleton] at hmax
  let C := centralizer ({t.val} : Set B)
  let Q := (U : Subgroup B) ⊓ C
  obtain ⟨P,hP⟩ := ((U.isPGroup'.to_le (show Q ≤ (U : Subgroup B) from inf_le_left)).comap_subtype
    (K := C)).exists_le_sylow
  have he : (P : Subgroup C).map C.subtype = Q := hmax _ (P.isPGroup'.map _) (by
    change Q ≤ _
    rw [← map_subgroupOf_eq_of_le (show Q ≤ C from inf_le_right)]
    exact map_mono hP) (map_subtype_le _)
  refine ⟨c,hc.symm ▸ t.property,?_⟩
  have hh : (fun x : B => ∃ P : Sylow 2 (centralizer ({x} : Set B)),
      (P : Subgroup _).map (centralizer ({x} : Set B)).subtype =
        (U : Subgroup B) ⊓ centralizer ({x} : Set B)) t.val := ⟨P,he⟩
  exact hc.symm ▸ hh

private theorem conjugate_residual {X Y : Type*} [Group X] [Group Y]
    (φ : X →* Y) (x g : X) (hx : φ x ∉ solvableResidual Y) :
    φ (g*x*g⁻¹) ∉ solvableResidual Y := by
  intro h
  have hh := (inferInstance : (solvableResidual Y).Normal).conj_mem _ h (φ g)⁻¹
  have he : (φ g)⁻¹ * φ (g*x*g⁻¹) * ((φ g)⁻¹)⁻¹ = φ x := by
    rw [map_mul,map_mul,map_inv]
    group
  exact hx (he ▸ hh)

private theorem conjugate_fixed
    {L B R X Y Z : Type*} [Group L] [Group B] [Group R] [Group X] [Group Y] [Group Z]
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam X Y Z} (b c : B) (y : Y)
    (h : ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) β,
      e.middle (centralPoint b) = y) :
    ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α (c*b*c⁻¹)) β,
      e.middle (centralPoint (c*b*c⁻¹)) = y := by
  obtain ⟨e,he⟩ := h
  refine ⟨(centralizerConjugate α b c).trans e,?_⟩
  change e.middle ((centralizerConjugate α b c).middle (centralPoint (c*b*c⁻¹))) = _
  rw [centralizerConjugate_self]
  exact he

private theorem saturate_fixed_diagram
    {L B R X Y Z : Type*} [Group L] [Group B] [Group R] [Finite B]
    [Group X] [Group Y] [Group Z]
    (α : RankTwoAmalgam L B R) (β : RankTwoAmalgam X Y Z) (U : Sylow 2 B) (y : Y)
    (h : ∃ b : B, b ∈ (U : Subgroup B) ∧ orderOf b = 2 ∧
      α.left b ∉ solvableResidual L ∧ α.right b ∉ solvableResidual R ∧
      ((∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) β,
          e.middle (centralPoint b) = y) ∨
       (∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) β.reverse,
          e.middle (centralPoint b) = y))) :
    ∃ b : B, b ∈ (U : Subgroup B) ∧ orderOf b = 2 ∧
      α.left b ∉ solvableResidual L ∧ α.right b ∉ solvableResidual R ∧
      (∃ P : Sylow 2 (centralizer ({b} : Set B)),
        (P : Subgroup _).map (centralizer ({b} : Set B)).subtype =
          (U : Subgroup B) ⊓ centralizer ({b} : Set B)) ∧
      ((∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) β,
          e.middle (centralPoint b) = y) ∨
       (∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) β.reverse,
          e.middle (centralPoint b) = y)) := by
  obtain ⟨b,hb,hb2,hl,hr,he⟩ := h
  obtain ⟨c,hcU,hcP⟩ := saturated_sylow U ⟨b,hb⟩
  refine ⟨c*b*c⁻¹,hcU,((MulAut.conj c).orderOf_eq b).trans hb2,
    conjugate_residual α.left b c hl,conjugate_residual α.right b c hr,hcP,?_⟩
  exact he.elim
    (fun h => Or.inl (conjugate_fixed (α := α) (β := β) b c _ h))
    (fun h => Or.inr (conjugate_fixed (α := α) (β := β.reverse) b c _ h))


/-- Choose the graph element with its centralizer Sylow in the original whole
middle group. Both fixed endpoint maps and the marked graph factor are retained. -/
theorem comparison_graph_saturated
    {L B R : Type*} [Group L] [Group B] [Group R] [Finite B]
    (α : RankTwoAmalgam L B R) (U : Sylow 2 B)
    (hc : Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse)) :
    ∃ b : B, b ∈ (U : Subgroup B) ∧ orderOf b = 2 ∧
      α.left b ∉ solvableResidual L ∧ α.right b ∉ solvableResidual R ∧
      (∃ P : Sylow 2 (centralizer ({b} : Set B)),
        (P : Subgroup _).map (centralizer ({b} : Set B)).subtype =
          (U : Subgroup B) ⊓ centralizer ({b} : Set B)) ∧
      ((∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m),
          e.middle (centralPoint b) = (1,UnitaryFourOuter.generator)) ∨
       (∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m).reverse,
          e.middle (centralPoint b) = (1,UnitaryFourOuter.generator))) := by
  exact saturate_fixed_diagram α (fixedDiagram m) U (1,UnitaryFourOuter.generator)
    (comparison_graph_sylow m hm α U hc)

private theorem sylow_card_transport {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (a : ℕ) (h : ∀ Q : Sylow 2 Y, Nat.card Q = a)
    (P : Sylow 2 X) : Nat.card P = a := by
  have he := h (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change Nat.card ((P : Subgroup X).map e.toMonoidHom) = a at he
  rwa [card_map_of_injective e.injective] at he

include hm in
/-- All three fixed groups have the same Sylow two-order; this is a statement
about the full fixed parabolics and full fixed overlap. -/
theorem fixed_diagram_sylow_card
    {L B R : Type*} [Group L] [Group B] [Group R] [Finite L] [Finite B] [Finite R]
    (α : RankTwoAmalgam L B R) (b : B)
    (he : Nonempty (RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m)) ∨
      Nonempty (RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m).reverse)) :
    (∀ P : Sylow 2 (centralizer ({α.left b} : Set L)), Nat.card P = 2*(2^m)^4) ∧
    (∀ P : Sylow 2 (centralizer ({b} : Set B)), Nat.card P = 2*(2^m)^4) ∧
    (∀ P : Sylow 2 (centralizer ({α.right b} : Set R)), Nat.card P = 2*(2^m)^4) := by
  have hpoint := fixedPoint_sylow_card (MatrixField m) (fieldConj m)
    (PointLocal.fixedField_card m hm) hm
  have hplane := fixedPlane_sylow_card (MatrixField m) (fieldConj m)
    (PointLocal.fixedField_card m hm) hm
  have hborel := fixedBorel_sylow_card (MatrixField m) (fieldConj m)
    (PointLocal.fixedField_card m hm) hm
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · exact ⟨sylow_card_transport e.left _ hpoint,
      sylow_card_transport e.middle _ hborel,sylow_card_transport e.right _ hplane⟩
  · exact ⟨sylow_card_transport e.left _ hplane,
      sylow_card_transport e.middle _ hborel,sylow_card_transport e.right _ hpoint⟩

private theorem forget_marking {X Y : Type*} (P : X → Prop) (Q : Y → Prop)
    (h : (∃ x, P x) ∨ (∃ y, Q y)) : Nonempty X ∨ Nonempty Y :=
  h.elim (fun hx => Or.inl hx.nonempty) (fun hy => Or.inr hy.nonempty)

include hm in
/-- Read the same counts directly from the marked fixed-diagram witness. -/
theorem fixed_diagram_sylow_card_marked
    {L B R : Type*} [Group L] [Group B] [Group R] [Finite L] [Finite B] [Finite R]
    (α : RankTwoAmalgam L B R) (b : B)
    (he : (∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m),
        e.middle (centralPoint b) = (1,UnitaryFourOuter.generator)) ∨
      (∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m).reverse,
        e.middle (centralPoint b) = (1,UnitaryFourOuter.generator))) :
    (∀ P : Sylow 2 (centralizer ({α.left b} : Set L)), Nat.card P = 2*(2^m)^4) ∧
    (∀ P : Sylow 2 (centralizer ({b} : Set B)), Nat.card P = 2*(2^m)^4) ∧
    (∀ P : Sylow 2 (centralizer ({α.right b} : Set R)), Nat.card P = 2*(2^m)^4) := by
  exact fixed_diagram_sylow_card m hm α b
    (forget_marking _ _ he)

include hm in
/-- Every Sylow of the marked graph-fixed middle has order 2q⁴, in either
orientation of the original comparison. -/
theorem fixed_middle_sylow_card
    {L B R : Type*} [Group L] [Group B] [Group R] [Finite B]
    (α : RankTwoAmalgam L B R) (b : B)
    (he : Nonempty (RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m)) ∨
      Nonempty (RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m).reverse))
    (P : Sylow 2 (centralizer ({b} : Set B))) : Nat.card P = 2*(2^m)^4 := by
  have eh : Nonempty (centralizer ({b} : Set B) ≃*
      ((Theory.SpecificGroups.SymplecticFour.borel (F := PointLocal.FixedField m)) × UnitaryFourOuter.C2)) :=
    he.elim (fun ⟨e⟩ => ⟨e.middle⟩) (fun ⟨e⟩ => ⟨e.middle⟩)
  obtain ⟨e⟩ := eh
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hq := fixedBorel_sylow_card (MatrixField m) (fieldConj m)
    (PointLocal.fixedField_card m hm) hm Q
  change Nat.card ((P : Subgroup _).map e.toMonoidHom) = _ at hq
  rwa [card_map_of_injective e.injective] at hq

end CFSG.Quasithin.ChapterF.UnitarySource.FourGraph
