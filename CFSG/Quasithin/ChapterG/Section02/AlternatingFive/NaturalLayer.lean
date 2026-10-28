module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Defs
public import Theory.Representation.SpecialLinearNatural

/-!
# The natural upper-module conclusion of G.2.4

This specifies an actual equivariant identification of S/S₂ with s copies
of the natural two-dimensional module over a field of order four. The
action is checked on representatives in S and thus cannot be replaced by
an unrelated action with the same dimensions. The orthogonal coordinates
on V_L remain in `Hypothesis`; these are different representations.

This module only defines the recognition output. Constructing it from
G.1.3 and the earlier G.2.4 clauses remains a separate proof obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(6), printed p.334.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G]

theorem I_normalizes_core (D : Setup G) (g : G) :
    D.I g ≤ normalizer (D.S g : Set G) := by
  have hm := (pCore 2 (D.I g)).le_normalizer_map (D.I g).subtype
  simpa only [Setup.S, pCoreIn, normalizer_eq_top,
    ← MonoidHom.range_eq_map, range_subtype] using hm

/-- The actual conjugation action on the subgroup S=O₂(I). -/
def coreConjugate (D : Setup G) (g : G) (i : D.I g) (x : D.S g) : D.S g :=
  ⟨(i : G) * x * (i : G)⁻¹,
    (mem_normalizer_iff.mp (I_normalizes_core D g i.property) x).mp x.property⟩

/-- An equivariant natural-module identification of the literal upper
quotient. This is a conclusion to be constructed, not a source hypothesis. -/
structure NaturalLayer (D : Setup G) (g : G) (F : Type*) [Field F]
    (s : ℕ) (hLI : D.L ≤ D.I g)
    [((S₂ D g).subgroupOf (D.S g)).Normal] where
  field_card : Nat.card F = 4
  model : D.star D.L ≃* SL(2, F)
  coordinates : UpperQuotient D g ≃* Multiplicative (Fin s → Fin 2 → F)
  action : D.I g →* MulAut (UpperQuotient D g)
  action_mk (i : D.I g) (x : D.S g) :
    action i (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) x) =
      QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) (coreConjugate D g i x)
  equivariant (l : D.L) (x : UpperQuotient D g) :
    (coordinates (action ⟨l, hLI l.property⟩ x)).toAdd =
      fun j => (model (starProjection D l)).val *ᵥ (coordinates x).toAdd j

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
