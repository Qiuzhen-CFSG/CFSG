module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Quintet

/-!
# The natural S5 quotient in H.15.4

These adapters provide the actual map on the five non-distinguished tetrads,
its equivariant linear marking of the top cocode quotient, and irreducibility.
The two earlier H.14 group-action facts remain explicit. The source's cubic
fixed-space datum is retained in a compatibility theorem giving two fixed
dimensions in both the middle term and the top quotient. Final H.15.4 assembly
and discharge of the earlier native inputs remain with their owning tasks.

Source: Aschbacher--Smith, H.15.4, printed p.400 (1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode MathieuCode.M22Quintet Representation.BinaryOffender
open MathieuCode.M22Quintet.CocodeTransfer

/-- The actual permutation of the five tetrads other than `{0,2,9,14}`. -/
abbrev m22Quintet_naturalQuotientMap : Q →* Equiv.Perm (Fin 5) := NaturalQuotient.q

/-- Tetrad parity followed by deleting the fixed tetrad coordinate. -/
def m22Quintet_naturalQuotientMarking :
    (M22Cocode ⧸ V6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
  NaturalQuotient.marking

theorem m22Quintet_naturalQuotientMarking_equivariant (g : Q) (v : M22Cocode ⧸ V6) :
    m22Quintet_naturalQuotientMarking (V6Subrepresentation.quotientRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (m22Quintet_naturalQuotientMap g)
        (m22Quintet_naturalQuotientMarking v) :=
  NaturalQuotient.marking_equivariant g v

/-- Earlier group identifications suffice; no M22 module conclusion is a premise. -/
theorem m22Quintet_natural_top_of_H14
    (hpart : (sextetPartPerm m22SourceSextet).ker.comap QToSextet = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5)) :
    Function.Surjective m22Quintet_naturalQuotientMap ∧
      m22Quintet_naturalQuotientMap.ker = K.subgroupOf Q ∧
      Representation.IsIrreducible V6Subrepresentation.quotientRepresentation :=
  ⟨NaturalQuotient.q_surjective hpart e, NaturalQuotient.q_ker hpart,
    NaturalQuotient.top_isIrreducible hpart e⟩

/-- The four fixed dimensions in the ten-dimensional source module split
as two in its literal middle subrepresentation and two in the top quotient. -/
theorem m22Quintet_natural_top_cubic_compatibility
    (hpart : (sextetPartPerm m22SourceSextet).ker.comap QToSextet = pCore 2 Q)
    (g : Q) (hg : orderOf g = 3)
    (hfour : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers g.val)) = 4) :
    Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.toRepresentation
      (Subgroup.zpowers g)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.quotientRepresentation
      (Subgroup.zpowers g)) = 2 :=
  NaturalQuotient.source_cubic_fixed_dimensions hpart g hg hfour

end CFSG.Quasithin.ChapterH.Section13To16
