module
public import Theory.GroupAction.IrreducibleNormalIntersection
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceOuterAction

/-!
# Frattini intersections after the intrinsic inner-action step

For a normal detected component, irreducibility puts its intersection
with the original complement in the Frattini subgroup unless it contains
the complement. The detected nontrivial action also puts the complement
centralizer in its Frattini subgroup. These are literal quotient images,
combined with the proved inner-action inclusion.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.510.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

theorem LocalInput.quotient_component_inf_le_frattini_or_le
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hn : (quotientImage H L).Normal) :
    quotientImage H P ⊓ quotientImage H L ≤
        (frattini (quotientImage H P)).map (quotientImage H P).subtype ∨
      quotientImage H P ≤ quotientImage H L := by
  let := hn
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) :=
    h.quotient_normalizer_irreducible
  exact hi.inf_normal_le_frattini_or_le _

theorem LocalInput.quotient_component_centralizer_le_frattini
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hL : ComponentDetection P H L) (hn : (quotientImage H L).Normal) :
    quotientImage H P ⊓ centralizer (quotientImage H L : Set (XiQuotient H)) ≤
      (frattini (quotientImage H P)).map (quotientImage H P).subtype := by
  let := hn
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) :=
    h.quotient_normalizer_irreducible
  exact hi.centralizer_le_frattini
    (hL.quotient_commutator_ne_bot h.complement_le_overgroup)

theorem LocalInput.normal_component_inner_action_and_intersections
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (quotientImage H L).Normal) :
    (quotientImage H P ≤ quotientImage H L ⊔
      centralizer (quotientImage H L : Set (XiQuotient H))) ∧
    (quotientImage H P ⊓ centralizer (quotientImage H L : Set (XiQuotient H)) ≤
      (frattini (quotientImage H P)).map (quotientImage H P).subtype) ∧
    ((quotientImage H P ⊓ quotientImage H L ≤
        (frattini (quotientImage H P)).map (quotientImage H P).subtype) ∨
      quotientImage H P ≤ quotientImage H L) :=
  ⟨h.quotient_complement_le_component_centralizer hA hC hH hL hn,
    h.quotient_component_centralizer_le_frattini hL hn,
    h.quotient_component_inf_le_frattini_or_le hn⟩

end CFSG.Quasithin.Chapter1.XiEmbedding
