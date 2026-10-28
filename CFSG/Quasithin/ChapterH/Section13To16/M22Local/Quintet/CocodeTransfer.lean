module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Quintet

/-!
# Conditional assembly of H.15.4 on the native outer M22 cocode

The actual sextet-part quotient proves top irreducibility, which completes the
strict chief flag and its dual-of-K and natural-S5 identifications. Faithful
full sextet transvections descend to the literal V6 with center V1. The common
four-subgroup uses the compatible sextet with first tetrad {0,2,9,14} and its
incident octad. Its middle fixed dimension five is proved from transvections;
the earlier ambient fixed dimension six then proves generation and xi.

`m22Quintet_cocode_H15_4_of_earlier` assembles all four cocode clauses, including
fixed dimension two for every hyperplane. The order-three datum remains explicit
and is checked against the geometric S5 action. No requested M22 conclusion or
intermediate top irreducibility is a premise of that theorem. The earlier M24,
H.14 and involution/cubic inputs must still be instantiated by the unconditional
source-theorem owner. The constructed flag and action data also supply the
published downstream interface for H.16.3.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.15.4, printed p.400.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode MathieuCode.M22Quintet Representation.BinaryOffender
open MathieuCode.M22Quintet.CocodeTransfer

/-- The lower-layer intersection is exactly the source intersection for the
compatible geometry, with each core relative to its own stabilizer. -/
theorem m22Quintet_compatible_common_eq :
    M22Quintet.CocodeTransfer.E24 =
      octadKernel m22SourceOctad ⊓ sextetKernel m22SourceSextet := rfl

/-- The genuine Q-equivariant third-isomorphism identification used to transfer
the M24 top factor to the outer M22 cocode. -/
theorem m22Quintet_top_quotient_equivariant (g : Q) (v : M22Cocode ⧸ V6) :
    M22Quintet.CocodeTransfer.topQuotientEquiv
        (V6Subrepresentation.quotientRepresentation g v) =
      M22Quintet.CocodeTransfer.U7Subrepresentation.quotientRepresentation g
        (M22Quintet.CocodeTransfer.topQuotientEquiv v) :=
  M22Quintet.CocodeTransfer.topQuotientEquiv_equivariant g v

/-- The four-subgroup and xi conclusions from ambient sextet/octad data.
The natural-quotient branch must still discharge the irreducibility premise. -/
theorem m22Quintet_four_generation_and_xi_of_M24_data
    [IsElementaryAbelian 2 K] (hK : 8 ≤ Nat.card K)
    (hKS : K ≤ (sextetKernel m22SourceSextet).comap m22PairStabilizer.subtype)
    (hmove : ∀ k ∈ sextetKernel m22SourceSextet, ∀ u ∈ U7,
      cocodeRepresentation k u - u ∈ sextetTetradLine m22SourceSextet)
    (hEK : M22Quintet.CocodeTransfer.E ≤ K)
    (hE : IsElementaryAbelian 2 M22Quintet.CocodeTransfer.E)
    (hcard : Nat.card M22Quintet.CocodeTransfer.E = 4)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation
        (octadKernel m22SourceOctad ⊓ sextetKernel m22SourceSextet)) = 6)
    (hmiddle : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation
        (octadKernel m22SourceOctad ⊓ sextetKernel m22SourceSextet) ⊓ U7 :
          Submodule (ZMod 2) Cocode) = 5)
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] :
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ ∧
      ∀ A : Subgroup m22PairStabilizer, A.relIndex K = 2 →
        fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ := by
  have hgen := M22Quintet.CocodeTransfer.fourFixedSpan_eq_top_of_sextet_data
    hK hKS hmove hEK hE hcard hfixed hmiddle
  exact ⟨hgen, fun A hA => fixedSpaceSpan_eq_top_of_fourFixedSpan _ hA hgen⟩

/-- The actual H.15.4 chief flag, constructed from the earlier actions.
In particular, its top irreducibility is proved rather than assumed. -/
@[expose] def m22Quintet_cocode_flag_of_earlier
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hpart : (sextetPartPerm m22SourceSextet).ker.comap QToSextet = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5)) : DualAction.CocodeFlag :=
  chiefFlagOfEarlierData D I hpart e

/-- The genuine equivariant identifications and faithful full transvection
action, in the published interface consumed by the H.16.3 duality proof. -/
@[expose] def m22Quintet_cocode_actions_of_earlier
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hpart : (sextetPartPerm m22SourceSextet).ker.comap QToSextet = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5)) :
    DualAction.CocodeActionData (m22Quintet_cocode_flag_of_earlier D I hpart e) (Additive K) :=
  actionDataOfEarlierData D I hpart e

/-- Complete conditional H.15.4: the native chief flag and action markings,
full center transvections, both hyperplane clauses and four-subgroup generation.
The extra cubic conclusion verifies the source datum in the actual S5 marking.
All premises concern the earlier M24, H.14, and involution/order-three facts. -/
theorem m22Quintet_cocode_H15_4_of_earlier
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hpart : (sextetPartPerm m22SourceSextet).ker.comap QToSextet = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5))
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (horder : orderOf i0 = 2)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i0)) = 5)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    [IsElementaryAbelian 2 E24] (hcard24 : Nat.card E24 = 4)
    (hcommon : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6)
    (hcubic : ∀ g : Q, orderOf g = 3 → Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers g.val)) = 4) :
    (∃ F : DualAction.CocodeFlag, Nonempty (DualAction.CocodeActionData F (Additive K))) ∧
    W1 = V1 ∧
    ((⊥ : Submodule (ZMod 2) M22Cocode) < V1 ∧ V1 < V2 ∧ V2 < V6 ∧ V6 < ⊤) ∧
    (Module.finrank (ZMod 2) V1 = 1 ∧ Module.finrank (ZMod 2) V2 = 2 ∧
      Module.finrank (ZMod 2) V6 = 6) ∧
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ ∧
    (∀ A : Subgroup m22PairStabilizer, A ≤ K → A.relIndex K = 2 →
      fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ ∧
        Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2) ∧
    (∀ g : Q, orderOf g = 3 →
      Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.toRepresentation
        (Subgroup.zpowers g)) = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace V6Subrepresentation.quotientRepresentation
        (Subgroup.zpowers g)) = 2) :=
  transfer_of_earlier_data D I hpart e hindecomp i0 hi0 hout horder hfixed
    hEK hE hcard hcard24 hcommon hcubic

end CFSG.Quasithin.ChapterH.Section13To16
