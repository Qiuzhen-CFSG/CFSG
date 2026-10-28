module

public import CFSG.Quasithin.ChapterB.Section02.Baumann.Defs
public import Theory.Representation.BinaryInternalFixedSpaceCodimension

/-!
# The dimension step in Baumann's argument

This adapter uses the published `fixedCodim`, the difference of base-two
logarithms of the orders of V and C_V(A). It identifies that number with
the dimension of the quotient by the fixed vectors of genuine conjugation.

For V ≤ W elementary abelian, the dimension bound on V and the generator
supplements imply C_W(L) = C_W(I) and W = C_W(L)V. Only I must normalize W;
ambient normality of W is neither assumed nor inferred. The parent B.2.18
argument supplies invariance, the supplements and L ≤ I, then consumes
these two identities in `alpha_decomposition_of_fixed_space`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.18,
printed p.81. This conditional dimension result is not the full B.2.18.
-/

namespace CFSG.Quasithin.ChapterB.BaumannArgument

open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The source codimension is the dimension of the actual internal fixed-space quotient. -/
public theorem fixedCodim_eq_internal_quotient_finrank (V I A : Subgroup G)
    [IsElementaryAbelian 2 V] (hI : I ≤ normalizer (V : Set G)) (hA : A ≤ I) :
    fixedCodim V A = Module.finrank (ZMod 2) (Additive V ⧸
      Representation.invariants
        ((Representation.BinaryInternalFixedSpaceCodimension.representation V I hI).comp
          (A.subgroupOf I).subtype)) :=
  Representation.BinaryInternalFixedSpaceCodimension.fixedCodim_eq_finrank V I A hI hA

variable {ι : Type*} [Fintype ι]

/-- The two fixed-space identities needed for the final alpha decomposition. -/
public theorem fixed_space_eq_and_supplement (V W : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (X : ι → Subgroup G) (L : Subgroup G) (hVW : V ≤ W)
    (hW : (⨆ i, X i) ≤ normalizer (W : Set G))
    (hL : L ≤ ⨆ i, X i)
    (hdim : (∑ i, fixedCodim V (X i)) ≤ fixedCodim V L)
    (hsupp : ∀ i, W = (W ⊓ centralizer (X i : Set G)) ⊔ V) :
    W ⊓ centralizer (L : Set G) = W ⊓ centralizer ((⨆ i, X i : Subgroup G) : Set G) ∧
      W = (W ⊓ centralizer (L : Set G)) ⊔ V :=
  Representation.BinaryInternalFixedSpaceCodimension.fixed_eq_and_supplement V W X L hVW
    le_normalizer_of_normal hW hL hdim hsupp

end CFSG.Quasithin.ChapterB.BaumannArgument
