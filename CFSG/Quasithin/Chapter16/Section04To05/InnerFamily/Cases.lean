module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Choice
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# The actual remaining models in the proof of 16.4.9

The graph-field condition identifies the quotient L/O₂(L) with the projective
matrix group PSL₃(4) and intertwines the action of the specified ambient element
with inverse transpose times Frobenius. Thus it retains the action, quotient
and embedding of L; it is not a group-family label. The alternating alternatives
identify L itself, so central covers are not silently included in those cases.

These are the targets of the outer-action reduction and the hypotheses of the
separate exceptional-case contradictions. No reduction or exclusion is asserted
by the definitions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), alternatives (i)–(ii), printed pp.1190–1192.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections

open Subgroup

variable {G : Type*} [Group G]

/-- A graph-field involution on the actual PSL₃(4) quotient. The order-two
condition on the ambient element is supplied by each application. -/
def IsL3FourGraphField (L : Subgroup G) (r : G) : Prop :=
  ∃ hr : r ∈ normalizer (L : Set G),
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL,
      ∀ x : L,
        e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom ⟨r, hr⟩ x)) =
          (Matrix.PSL3.OuterSolvable.graph Matrix.PSL3Four.F * Matrix.PSL3Four.pslFrobenius)
            (e (QuotientGroup.mk' (pCore 2 L) x))

/-- The two remaining source alternatives, expressed by actual model maps. -/
def InnerFamilyExceptionalCase (L : Subgroup G) (r : G) : Prop :=
  (Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (L ≃* alternatingGroup (Fin 8))) ∨ IsL3FourGraphField L r

end CFSG.Quasithin.Chapter16.Intersections
